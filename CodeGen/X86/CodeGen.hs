{-# language LambdaCase #-}
{-# language BangPatterns #-}
{-# language ViewPatterns #-}
{-# language PatternGuards #-}
{-# language PatternSynonyms #-}
{-# language NoMonomorphismRestriction #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language TypeFamilies #-}
{-# language GADTs #-}
{-# language DataKinds #-}
{-# language KindSignatures #-}
{-# language PolyKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
module CodeGen.X86.CodeGen where

import Numeric
import Data.Maybe
import Data.Monoid
import qualified Data.Vector as V
import Data.Bits
import Data.Int
import Data.Word
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Debug.Trace

import CodeGen.X86.Asm

------------------------------------------------------- utils

takes [] _ = []
takes (i: is) xs = take i xs: takes is (drop i xs)

iff b a = if b then a else mempty

indicator :: Integral a => Bool -> a
indicator False = 0x0
indicator True  = 0x1

pattern FJust a = First (Just a)
pattern FNothing = First Nothing

integralToBytes :: (Bits a, Integral a) => Bool{-signed-} -> Size -> a -> Maybe Bytes
integralToBytes False S64 w = toBytes <$> (toIntegralSized w :: Maybe Word64)
integralToBytes False S32 w = toBytes <$> (toIntegralSized w :: Maybe Word32)
integralToBytes False S16 w = toBytes <$> (toIntegralSized w :: Maybe Word16)
integralToBytes False S8  w = toBytes <$> (toIntegralSized w :: Maybe Word8)
integralToBytes True  S64 w = toBytes <$> (toIntegralSized w :: Maybe Int64)
integralToBytes True  S32 w = toBytes <$> (toIntegralSized w :: Maybe Int32)
integralToBytes True  S16 w = toBytes <$> (toIntegralSized w :: Maybe Int16)
integralToBytes True  S8  w = toBytes <$> (toIntegralSized w :: Maybe Int8)

------------------------------------------------------- register packed with its size

data SReg where
    SReg :: IsSize s => Reg s -> SReg

phisicalReg :: SReg -> Reg S64
phisicalReg (SReg (HighReg x)) = NormalReg x
phisicalReg (SReg (NormalReg x)) = NormalReg x

isHigh (SReg HighReg{}) = True
isHigh _ = False

regs :: IsSize s => Operand r s -> [SReg]
regs = \case
    MemOp (Addr r _ i) -> foldMap (pure . SReg) r ++ foldMap (pure . SReg . snd) i
    RegOp r -> [SReg r]
    _ -> mempty

isRex (SReg x@(NormalReg r)) = r .&. 0x8 /= 0 || size x == S8 && r `shiftR` 2 == 1
isRex _ = False

noHighRex r = not $ any isHigh r && any isRex r

no64 S64 = S32
no64 s = s

------------------------------------------------------- code builder

data CodeBuilder
    = CodeBuilder !Int !Int (CodeBuilderState -> (CodeBuilderRes, CodeBuilderState))

pattern ExactCodeBuilder len f <- (getExactCodeBuilder -> Just (len, f))
  where ExactCodeBuilder len f = CodeBuilder len len $ \st@(n, _) -> second ((,) (n + len)) $ f st

getExactCodeBuilder (CodeBuilder i j f) | i == j = Just (i, second snd . f)
getExactCodeBuilder _ = Nothing

codeBuilderLength (ExactCodeBuilder len _) = len

buildCode :: CodeBuilder -> CodeBuilderState -> (CodeBuilderRes, CodeBuilderState)
buildCode (CodeBuilder _ _ f) st = f st

mapLabelState g (CodeBuilder i j f) = CodeBuilder i j $ \(n, g -> (fx, xs)) -> second (second fx) $ f (n, xs)

censorCodeBuilder g (CodeBuilder i j f) = CodeBuilder i j $ \st -> first (g st) $ f st

type CodeBuilderRes = [Either Int (Int, Word8)]

type CodeBuilderState = (Int, LabelState)

type LabelState = [Either [(Size, Int, Int)] Int]

instance Monoid CodeBuilder where
    mempty = ExactCodeBuilder 0 $ \(_, st) -> (mempty, st)
    f `mappend` g = CodeBuilder (i1+i2) (j1+j2) $ \(buildCode f -> (a, buildCode g -> (b, st))) -> (a ++ b, st)
      where
        (i1, j1) = bounds f
        (i2, j2) = bounds g

bounds (CodeBuilder i j _) = (i, j)

codeByte :: Word8 -> CodeBuilder
codeByte c = ExactCodeBuilder 1 $ \(n, labs) -> ([Right (n, c)], labs)

mkRef :: Size -> Int -> Int -> CodeBuilder
mkRef s@(sizeLen -> sn) offset bs = ExactCodeBuilder sn f
  where
    f (n, labs) | bs >= length labs = error "missing scope"
    f (n, labs) = case labs !! bs of
        Right i -> (Right <$> zip [n..] z, labs)
          where
            vx = i - n - offset
            z = getBytes $ case s of
                S8  -> case vx of
                    Integral j -> toBytes (j :: Int8)
                    _ -> error $ show vx ++ " does not fit into an Int8"
                S32  -> case vx of
                    Integral j -> toBytes (j :: Int32)
                    _ -> error $ show vx ++ " does not fit into an Int32"
        Left cs -> (mempty, labs')
          where
            labs' = take bs labs ++ Left ((s, n, - n - offset): cs): drop (bs + 1) labs

mkAutoRef :: [(Size, Bytes)] -> Int -> Int -> CodeBuilder
mkAutoRef ss offset bs = CodeBuilder (minimum sizes) (maximum sizes) f
  where
    sizes = map (\(s, c) -> sizeLen s + bytesCount c) ss

    f (n, labs) | bs >= length labs = error "missing scope"
    f (n, labs) = case labs !! bs of
        Left cs -> error "auto length computation for forward references is not supported"
        Right i -> (Right <$> zip [n..] z, (n + length z, labs))
          where
            vx = i - n - offset
            z = g ss

            g [] = error $ show vx ++ " does not fit into auto size"
            g ((s, c): ss) = case (s, vx - bytesCount c - sizeLen s) of
                (S8,  Integral j) -> getBytes $ c <> toBytes (j :: Int8)
                (S32, Integral j) -> getBytes $ c <> toBytes (j :: Int32)
                _ -> g ss

------------------------------------------------------- code to code builder

instance Show Code where
    show c = unlines $ zipWith3 showLine is (takes (zipWith (-) (tail is ++ [s]) is) bs) ss
      where
        ss = snd . runWriter . flip evalStateT 0 . flip runReaderT [] . showCode $ c
        (x, s) = second fst $ buildCode (mkCodeBuilder c) (0, replicate 10{-TODO-} $ Left [])
        bs = V.toList $ V.replicate s 0 V.// [p | Right p <- x]
        is = [i | Left i <- x]

        showLine addr [] s = s
        showLine addr bs s = [showNibble i addr | i <- [5,4..0]] ++ " " ++ pad (2 * maxbytes) (concatMap showByte bs) ++ " " ++ s

        pad i xs = xs ++ replicate (i - length xs) ' '

        maxbytes = 12

codeBytes c = Bytes $ V.toList $ V.replicate s 0 V.// [p | Right p <- x]
  where
    (x, s) = buildTheCode c

buildTheCode x = second fst $ buildCode (mkCodeBuilder x) (0, [])

bytesToCodeBuilder :: Bytes -> CodeBuilder
bytesToCodeBuilder x = ExactCodeBuilder (bytesCount x) $ \(n, labs) -> (Right <$> zip [n..] (getBytes x), labs)

mkCodeBuilder :: Code -> CodeBuilder
mkCodeBuilder = \case
    EmptyCode -> mempty
    AppendCode cb _ _ -> cb

    Up a -> mapLabelState (\(x: xs) -> ((x:), xs)) $ mkCodeBuilder a

    Scope x -> ExactCodeBuilder 0 begin <> mkCodeBuilder x <> ExactCodeBuilder 0 end
      where
        begin (n, labs) = (mempty, Left []: labs)
        end (n, Right _: labs) = (mempty, labs)
        end (n, _: labs) = trace "warning: missing label" (mempty, labs)

    CodeLine_ cb _ -> censorCodeBuilder (\(addr, _) -> (Left addr:)) cb

mkCodeBuilder' :: CodeLine -> CodeBuilder
mkCodeBuilder' = \case
    Add_  a b -> op2 0x0 a b
    Or_   a b -> op2 0x1 a b
    Adc_  a b -> op2 0x2 a b
    Sbb_  a b -> op2 0x3 a b
    And_  a b -> op2 0x4 a b
    Sub_  a b -> op2 0x5 a b
    Xor_  a b -> op2 0x6 a b
    Cmp_  a b -> op2 0x7 a b

    Rol_ a b -> shiftOp 0x0 a b
    Ror_ a b -> shiftOp 0x1 a b
    Rcl_ a b -> shiftOp 0x2 a b
    Rcr_ a b -> shiftOp 0x3 a b
    Shl_ a b -> shiftOp 0x4 a b -- sal
    Shr_ a b -> shiftOp 0x5 a b
    Sar_ a b -> shiftOp 0x7 a b

    Xchg_ x@RegA r -> xchg_a r
    Xchg_ r x@RegA -> xchg_a r
    Xchg_ dest src -> op2' 0x43 dest' src
      where
        (dest', src') = if isMemOp src then (src, dest) else (dest, src)

    Test_ dest (mkImmNo64 (size dest) -> FJust (_, im)) -> case dest of
        RegA -> regprefix'' dest 0x54 mempty im
        _ -> regprefix'' dest 0x7b (reg8 0x0 dest) im
    Test_ dest (noImm "" -> src) -> op2' 0x42 dest' src'
      where
        (dest', src') = if isMemOp src then (src, dest) else (dest, src)

    Mov_ dest@(RegOp r) ((if size dest == S64 then mkImm S32 <> mkImmS S32 <> mkImmS S64 else mkImmS (size dest)) -> FJust ((se, si), im))
        | (se, si, size dest) /= (True, S32, S64) -> regprefix si dest (oneReg (0x16 .|. indicator (size dest /= S8)) r) im
        | otherwise -> regprefix'' dest 0x63 (reg8 0x0 dest) im
    Mov_ dest@(size -> s) (mkImmNo64 s -> FJust (_, im)) -> regprefix'' dest 0x63 (reg8 0x0 dest) im
    Mov_ dest src -> op2' 0x44 dest $ noImm (show (dest, src)) src

    Cmov_ (Condition c) dest src | size dest /= S8 -> regprefix2 src dest $ codeByte 0x0f <> codeByte (0x40 .|. c) <> reg2x8 dest src

    Lea_ dest src | size dest /= S8 -> regprefix2' (resizeOperand' dest src) dest 0x46 $ reg2x8 dest src
      where
        resizeOperand' :: IsSize s1 => Operand x s1 -> Operand RW s2 -> Operand RW s1
        resizeOperand' _ = resizeOperand

    Not_  a -> op1 0x7b 0x2 a
    Neg_  a -> op1 0x7b 0x3 a
    Inc_  a -> op1 0x7f 0x0 a
    Dec_  a -> op1 0x7f 0x1 a
    Call_ a -> op1' 0xff 0x2 a
    Jmpq_ a -> op1' 0xff 0x4 a

    Movd_ a@OpXMM b -> sse 0x6e a b
    Movd_ b a@OpXMM -> sse 0x7e a b
    Movq_ b a@OpXMM -> sse 0xd6 a b
    Movdqa_ a@OpXMM b -> sse 0x6f a b
    Movdqa_ b a@OpXMM -> sse 0x7f a b
    Paddb_  a b -> sse 0xfc a b
    Paddw_  a b -> sse 0xfd a b
    Paddd_  a b -> sse 0xfe a b
    Paddq_  a b -> sse 0xd4 a b
    Psubb_  a b -> sse 0xf8 a b
    Psubw_  a b -> sse 0xf9 a b
    Psubd_  a b -> sse 0xfa a b
    Psubq_  a b -> sse 0xfb a b
    Pxor_   a b -> sse 0xef a b
    Psllw_  a b -> sseShift 0x71 0x2 0xd1 a b
    Pslld_  a b -> sseShift 0x72 0x2 0xd2 a b
    Psllq_  a b -> sseShift 0x73 0x2 0xd3 a b
    Pslldq_ a b -> sseShift 0x73 0x7 undefined a b
    Psrlw_  a b -> sseShift 0x71 0x6 0xf1 a b
    Psrld_  a b -> sseShift 0x72 0x6 0xf2 a b
    Psrlq_  a b -> sseShift 0x73 0x6 0xf3 a b
    Psrldq_ a b -> sseShift 0x73 0x3 undefined a b
    Psraw_  a b -> sseShift 0x71 0x4 0xe1 a b
    Psrad_  a b -> sseShift 0x72 0x4 0xe2 a b

    Pop_ dest@(RegOp r) -> regprefix S32 dest (oneReg 0x0b r) mempty
    Pop_ dest -> regprefix S32 dest (codeByte 0x8f <> reg8 0x0 dest) mempty

    Push_ (mkImmS S8 -> FJust (_, im))  -> codeByte 0x6a <> im
    Push_ (mkImmS S32 -> FJust (_, im)) -> codeByte 0x68 <> im
    Push_ dest@(RegOp r) -> regprefix S32 dest (oneReg 0x0a r) mempty
    Push_ dest -> regprefix S32 dest (codeByte 0xff <> reg8 0x6 dest) mempty

    Ret_   -> codeByte 0xc3
    Nop_   -> codeByte 0x90
    PushF_ -> codeByte 0x9c
    PopF_  -> codeByte 0x9d
    Cmc_   -> codeByte 0xf5
    Clc_   -> codeByte 0xf8
    Stc_   -> codeByte 0xf9
    Cli_   -> codeByte 0xfa
    Sti_   -> codeByte 0xfb
    Cld_   -> codeByte 0xfc
    Std_   -> codeByte 0xfd

    J_ (Condition c) (Just S8)  -> codeByte (0x70 .|. c) <> mkRef S8 1 0
    J_ (Condition c) (Just S32) -> codeByte 0x0f <> codeByte (0x80 .|. c) <> mkRef S32 4 0
    J_ (Condition c) Nothing    -> mkAutoRef [(S8, Bytes [0x70 .|. c]), (S32, Bytes [0x0f, 0x80 .|. c])] 0 0

    Jmp_ (Just S8)  -> codeByte 0xeb <> mkRef S8 1 0
    Jmp_ (Just S32) -> codeByte 0xe9 <> mkRef S32 4 0
    Jmp_ Nothing    -> mkAutoRef [(S8, Bytes [0xeb]), (S32, Bytes [0xe9])] 0 0

    Label_ -> ExactCodeBuilder 0 lab
      where
        lab :: CodeBuilderState -> (CodeBuilderRes, LabelState)
        lab (n, labs) = (Right <$> concatMap g corr, labs')
          where
            (corr, labs') = replL (Right n) labs

            g (size, p, v) = zip [p..] $ getBytes $ case (size, v + n) of
                (S8, Integral v) -> toBytes (v :: Int8)
                (S32, Integral v) -> toBytes (v :: Int32)
                (s, i) -> error $ show i ++ " doesn't fit into " ++ show s

            replL x (Left z: zs) = (z, x: zs)
            replL x (z: zs) = second (z:) $ replL x zs

    Data_ x -> bytesToCodeBuilder x
    Align_ s -> CodeBuilder 0 s $ \(n, labs) -> let
                    n' = fromIntegral $ ((fromIntegral n - 1 :: Int64) .|. (fromIntegral s - 1)) + 1
                in (Right <$> zip [n..] (replicate (n' - n) 0x90), (n', labs))
  where
    convertImm :: Bool{-signed-} -> Size -> Operand r s -> First ((Bool, Size), CodeBuilder)
    convertImm a b (ImmOp (Immediate c)) = First $ (,) (a, b) . bytesToCodeBuilder <$> integralToBytes a b c
    convertImm True b (ImmOp (LabelRelValue s d)) | b == s = FJust $ (,) (True, b) $ mkRef s (sizeLen s) d
    convertImm _ _ _ = FNothing

    mkImmS, mkImm, mkImmNo64 :: Size -> Operand r s -> First ((Bool, Size), CodeBuilder)
    mkImmS = convertImm True
    mkImm  = convertImm False
    mkImmNo64 s = mkImmS (no64 s)

    xchg_a :: IsSize s => Operand r s -> CodeBuilder
    xchg_a dest@(RegOp r) | size dest /= S8 = regprefix (size dest) dest (oneReg 0x12 r) mempty
    xchg_a dest = regprefix'' dest 0x43 (reg8 0x0 dest) mempty

    toCode :: HasBytes a => a -> CodeBuilder
    toCode = bytesToCodeBuilder . toBytes

    sizePrefix_ :: [SReg] -> Size -> Operand r s -> Word8 -> CodeBuilder -> CodeBuilder -> CodeBuilder
    sizePrefix_ rs s r x c im
        | noHighRex rs = pre <> c <> displacement r <> im
        | otherwise = error "cannot use high register in rex instruction"
      where
        pre = case s of
            S8  -> mem32pre r <> maybePrefix40
            S16 -> codeByte 0x66 <> mem32pre r <> prefix40 x
            S32 -> mem32pre r <> prefix40 x
            S64 -> mem32pre r <> prefix40 (0x8 .|. x)
            S128 -> mem32pre r <> codeByte 0x66 <> maybePrefix40

        mem32pre :: Operand r s -> CodeBuilder
        mem32pre (MemOp r@Addr{}) | size r == S32 = codeByte 0x67
        mem32pre _ = mempty

        prefix40 x = iff (x /= 0) $ prefix40_ x
        prefix40_ x = codeByte $ 0x40 .|. x

        maybePrefix40 = iff (any isRex rs || x /= 0) (prefix40_ x)

        displacement :: Operand r s -> CodeBuilder
        displacement (IPMemOp (Immediate d)) = toCode d
        displacement (IPMemOp (LabelRelValue s@S32 d)) = mkRef s (sizeLen s + fromIntegral (codeBuilderLength im)) d
        displacement (MemOp (Addr b d i)) = mkSIB b i <> dispVal b d
          where
            mkSIB _ (IndexReg s (NormalReg 0x4)) = error "sp cannot be used as index"
            mkSIB _ (IndexReg s i) = f s $ reg8_ i
            mkSIB Nothing _ = f s1 0x4
            mkSIB (Just (reg8_ -> 0x4)) _ = f s1 0x4
            mkSIB _ _ = mempty

            f (Scale s) i = codeByte $ s `shiftL` 6 .|. i `shiftL` 3 .|. maybe 0x5 reg8_ b

            dispVal Just{} (Disp (Integral (d :: Int8))) = toCode d
            dispVal _ (Disp d) = toCode d
            dispVal Nothing _ = toCode (0 :: Int32)      -- [rbp] --> [rbp + 0]
            dispVal (Just (reg8_ -> 0x5)) _ = codeByte 0      -- [rbp] --> [rbp + 0]
            dispVal _ _ = mempty
        displacement _ = mempty

    reg8_ :: Reg t -> Word8
    reg8_ (NormalReg r) = r .&. 0x7
    reg8_ (HighReg r) = r .|. 0x4
    reg8_ (XMM r) = r .&. 0x7

    regprefix :: IsSize s => Size -> Operand r s -> CodeBuilder -> CodeBuilder -> CodeBuilder
    regprefix s r c im = sizePrefix_ (regs r) s r (extbits r) c im

    regprefix2 :: (IsSize s1, IsSize s) => Operand r1 s1 -> Operand r s -> CodeBuilder -> CodeBuilder
    regprefix2 r r' c = sizePrefix_ (regs r <> regs r') (size r) r (extbits r' `shiftL` 2 .|. extbits r) c mempty

    regprefix'' :: IsSize s => Operand r s -> Word8 -> CodeBuilder -> CodeBuilder -> CodeBuilder
    regprefix'' r p c = regprefix (size r) r $ extension r p <> c

    regprefix2' :: (IsSize s1, IsSize s) => Operand r1 s1 -> Operand r s -> Word8 -> CodeBuilder -> CodeBuilder
    regprefix2' r r' p c = regprefix2 r r' $ extension r p <> c

    sse :: IsSize s => Word8 -> Operand r S128 -> Operand r' s -> CodeBuilder
    sse op a@OpXMM b = regprefix S128 b (codeByte 0x0f <> codeByte op <> reg2x8 a b) mempty

    sseShift :: Word8 -> Word8 -> Word8 -> Operand RW S128 -> Operand r S8 -> CodeBuilder
    sseShift op x op' a@OpXMM b@(mkImm S8 -> FJust (_, i)) = regprefix S128 b (codeByte 0x0f <> codeByte op <> reg8 x a) i
    -- TODO: xmm argument

    extension :: HasSize a => a -> Word8 -> CodeBuilder
    extension x p = codeByte $ p `shiftL` 1 .|. indicator (size x /= S8)

    extbits :: Operand r s -> Word8
    extbits = \case
        MemOp (Addr b _ i) -> maybe 0 indexReg b .|. maybe 0 ((`shiftL` 1) . indexReg . snd) i
        RegOp r -> indexReg r
        _ -> 0
      where
        indexReg (NormalReg r) = r `shiftR` 3 .&. 1
        indexReg _ = 0

    reg8 :: Word8 -> Operand r s -> CodeBuilder
    reg8 w x = codeByte $ operMode x `shiftL` 6 .|. w `shiftL` 3 .|. rc x
      where
        operMode :: Operand r s -> Word8
        operMode (MemOp (Addr (Just (reg8_ -> 0x5)) NoDisp _)) = 0x1   -- [rbp] --> [rbp + 0]
        operMode (MemOp (Addr Nothing _ _)) = 0x0
        operMode (MemOp (Addr _ NoDisp _))  = 0x0
        operMode (MemOp (Addr _ (Disp (Integral (_ :: Int8))) _))  = 0x1
        operMode (MemOp (Addr _ Disp{} _))  = 0x2
        operMode IPMemOp{}                  = 0x0
        operMode _                          = 0x3

        rc :: Operand r s -> Word8
        rc (MemOp (Addr (Just r) _ NoIndex)) = reg8_ r
        rc MemOp{}   = 0x04      -- SIB byte
        rc IPMemOp{} = 0x05
        rc (RegOp r) = reg8_ r

    op2 :: IsSize s => Word8 -> Operand RW s -> Operand r s -> CodeBuilder
    op2 op dest@RegA src@(mkImmNo64 (size dest) -> FJust (_, im)) | size dest == S8 || isNothing (getFirst $ mkImmS S8 src)
        = regprefix'' dest (op `shiftL` 2 .|. 0x2) mempty im
    op2 op dest (mkImmS S8 <> mkImmNo64 (size dest) -> FJust ((_, k), im))
        = regprefix'' dest (0x40 .|. indicator (size dest /= S8 && k == S8)) (reg8 op dest) im
    op2 op dest src = op2' (op `shiftL` 2) dest $ noImm "1" src

    noImm :: String -> Operand r s -> Operand RW s
    noImm _ (RegOp r) = RegOp r
    noImm _ (MemOp a) = MemOp a
    noImm _ (IPMemOp a) = IPMemOp a
    noImm er _ = error $ "immediate value of this size is not supported: " ++ er

    op2' :: IsSize s => Word8 -> Operand RW s -> Operand RW s -> CodeBuilder
    op2' op dest src@RegOp{} = op2g op dest src
    op2' op dest@RegOp{} src = op2g (op .|. 0x1) src dest

    op2g :: (IsSize t, IsSize s) => Word8 -> Operand r s -> Operand r' t -> CodeBuilder
    op2g op dest src = regprefix2' dest src op $ reg2x8 src dest

    reg2x8 :: (IsSize s, IsSize s') => Operand r s -> Operand r' s' -> CodeBuilder
    reg2x8 (RegOp r) x = reg8 (reg8_ r) x

    op1_ :: IsSize s => Word8 -> Word8 -> Operand r s -> CodeBuilder -> CodeBuilder
    op1_ r1 r2 dest im = regprefix'' dest r1 (reg8 r2 dest) im

    op1 :: IsSize s => Word8 -> Word8 -> Operand r s -> CodeBuilder
    op1 a b c = op1_ a b c mempty

    op1' :: Word8 -> Word8 -> Operand RW S64 -> CodeBuilder
    op1' r1 r2 dest = regprefix S32 dest (codeByte r1 <> reg8 r2 dest) mempty

    shiftOp :: IsSize s => Word8 -> Operand RW s -> Operand r S8 -> CodeBuilder
    shiftOp c dest (ImmOp (Immediate 1)) = op1 0x68 c dest
    shiftOp c dest (mkImm S8 -> FJust (_, i)) = op1_ 0x60 c dest i
    shiftOp c dest RegCl = op1 0x69 c dest
    shiftOp _ _ _ = error "invalid shift operands"

    oneReg :: Word8 -> Reg t -> CodeBuilder
    oneReg x r = codeByte $ x `shiftL` 3 .|. reg8_ r

pattern OpXMM <- RegOp XMM{}

-------------------------------------------------------------- asm codes

data Code where
    Scope       :: Code -> Code
    Up          :: Code -> Code
    EmptyCode   :: Code
    AppendCode  :: CodeBuilder -> Code -> Code -> Code
    CodeLine_   :: CodeBuilder -> CodeLine -> Code

instance Monoid Code where
    mempty  = EmptyCode
    mappend a b = AppendCode (mkCodeBuilder a <> mkCodeBuilder b) a b

pattern CodeLine x <- CodeLine_ _ x
  where CodeLine x =  CodeLine_ (mkCodeBuilder' x) x

pattern Ret = CodeLine Ret_
pattern Nop = CodeLine Nop_
pattern PushF = CodeLine PushF_
pattern PopF = CodeLine PopF_
pattern Cmc = CodeLine Cmc_
pattern Clc = CodeLine Clc_
pattern Stc = CodeLine Stc_
pattern Cli = CodeLine Cli_
pattern Sti = CodeLine Sti_
pattern Cld = CodeLine Cld_
pattern Std = CodeLine Std_
pattern Inc a = CodeLine (Inc_ a)
pattern Dec a = CodeLine (Dec_ a)
pattern Not a = CodeLine (Not_ a)
pattern Neg a = CodeLine (Neg_ a)
pattern Add a b = CodeLine (Add_ a b)
pattern Or  a b = CodeLine (Or_  a b)
pattern Adc a b = CodeLine (Adc_ a b)
pattern Sbb a b = CodeLine (Sbb_ a b)
pattern And a b = CodeLine (And_ a b)
pattern Sub a b = CodeLine (Sub_ a b)
pattern Xor a b = CodeLine (Xor_ a b)
pattern Cmp a b = CodeLine (Cmp_ a b)
pattern Test a b = CodeLine (Test_ a b)
pattern Mov a b = CodeLine (Mov_ a b)
pattern Cmov c a b = CodeLine (Cmov_ c a b)
pattern Rol a b = CodeLine (Rol_ a b)
pattern Ror a b = CodeLine (Ror_ a b)
pattern Rcl a b = CodeLine (Rcl_ a b)
pattern Rcr a b = CodeLine (Rcr_ a b)
pattern Shl a b = CodeLine (Shl_ a b)
pattern Shr a b = CodeLine (Shr_ a b)
pattern Sar a b = CodeLine (Sar_ a b)
pattern Xchg a b = CodeLine (Xchg_ a b)
pattern Movd   a b = CodeLine (Movd_   a b)
pattern Movq   a b = CodeLine (Movq_   a b)
pattern Movdqa a b = CodeLine (Movdqa_ a b)
pattern Paddb  a b = CodeLine (Paddb_  a b)
pattern Paddw  a b = CodeLine (Paddw_  a b)
pattern Paddd  a b = CodeLine (Paddd_  a b)
pattern Paddq  a b = CodeLine (Paddq_  a b)
pattern Psubb  a b = CodeLine (Psubb_  a b)
pattern Psubw  a b = CodeLine (Psubw_  a b)
pattern Psubd  a b = CodeLine (Psubd_  a b)
pattern Psubq  a b = CodeLine (Psubq_  a b)
pattern Pxor   a b = CodeLine (Pxor_   a b)
pattern Psllw  a b = CodeLine (Psllw_  a b)
pattern Pslld  a b = CodeLine (Pslld_  a b)
pattern Psllq  a b = CodeLine (Psllq_  a b)
pattern Pslldq a b = CodeLine (Pslldq_ a b)
pattern Psrlw  a b = CodeLine (Psrlw_  a b)
pattern Psrld  a b = CodeLine (Psrld_  a b)
pattern Psrlq  a b = CodeLine (Psrlq_  a b)
pattern Psrldq a b = CodeLine (Psrldq_ a b)
pattern Psraw  a b = CodeLine (Psraw_  a b)
pattern Psrad  a b = CodeLine (Psrad_  a b)
pattern Lea a b = CodeLine (Lea_ a b)
pattern J a b = CodeLine (J_ a b)
pattern Pop a = CodeLine (Pop_ a)
pattern Push a = CodeLine (Push_ a)
pattern Call a = CodeLine (Call_ a)
pattern Jmpq a = CodeLine (Jmpq_ a)
pattern Jmp a  = CodeLine (Jmp_  a)
pattern Data a = CodeLine (Data_ a)
pattern Align a = CodeLine (Align_ a)
pattern Label = CodeLine (Label_)

-------------

showCode = \case
    EmptyCode  -> return ()
    AppendCode _ a b -> showCode a >> showCode b

    Scope c -> get >>= \i -> put (i+1) >> local (i:) (showCode c)

    Up c -> local tail $ showCode c

    CodeLine x -> showCodeLine x

