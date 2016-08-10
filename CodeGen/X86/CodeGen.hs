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

pattern Integral xs <- (toIntegralSized -> Just xs)

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

regs :: forall s k . IsSize s => Operand s k -> [SReg]
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
    = CodeBuilder (CodeBuilderState -> (CodeBuilderRes, CodeBuilderState))
    | ExactCodeBuilder Int (CodeBuilderState -> (CodeBuilderRes, LabelState))   -- ^ CodeBuilder with known length

codeBuilderLength (ExactCodeBuilder len _) = len

buildCode :: CodeBuilder -> CodeBuilderState -> (CodeBuilderRes, CodeBuilderState)
buildCode (CodeBuilder f) st = f st
buildCode (ExactCodeBuilder len f) (n, st) = second ((,) (n + len)) $ f (n, st)

mapLabelState g (CodeBuilder f) = CodeBuilder $ \(n, g -> (fx, xs)) -> second (second fx) $ f (n, xs)
mapLabelState g (ExactCodeBuilder len f) = ExactCodeBuilder len $ \(n, g -> (fx, xs)) -> second fx $ f (n, xs)

censorCodeBuilder g (CodeBuilder f) = CodeBuilder $ \st -> first (g st) $ f st
censorCodeBuilder g (ExactCodeBuilder len f) = ExactCodeBuilder len $ \st -> first (g st) $ f st

type CodeBuilderRes = [Either Int (Int, Word8)]

type CodeBuilderState = (Int, LabelState)

type LabelState = [Either [(Size, Int, Int)] Int]

instance Monoid CodeBuilder where
    mempty = ExactCodeBuilder 0 $ \(_, st) -> (mempty, st)
    ExactCodeBuilder len f `mappend` ExactCodeBuilder len' g = ExactCodeBuilder (len + len') $ \st -> let
            (a, st') = f st
            (b, st'') = g (len + fst st, st')
        in (a ++ b, st'')
    f `mappend` g = CodeBuilder $ \(buildCode f -> (a, buildCode g -> (b, st))) -> (a ++ b, st)

codeByte :: Word8 -> CodeBuilder
codeByte c = ExactCodeBuilder 1 $ \(n, labs) -> ([Right (n, c)], labs)

mkRef :: Size -> Int -> Int -> CodeBuilder
mkRef s@(sizeLen -> sn) offset bs = ExactCodeBuilder sn f
  where
    f (n, labs) | bs >= length labs = trace "warning: missing scope" (mempty, labs) 
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
    AppendCode a b -> mkCodeBuilder a <> mkCodeBuilder b

    Up a -> mapLabelState (\(x: xs) -> ((x:), xs)) $ mkCodeBuilder a

    Scope x -> ExactCodeBuilder 0 begin <> mkCodeBuilder x <> ExactCodeBuilder 0 end
      where
        begin (n, labs) = (mempty, Left []: labs)
        end (n, Right _: labs) = (mempty, labs)
        end (n, _: labs) = trace "warning: missing label" (mempty, labs)

    x -> censorCodeBuilder (\(addr, _) -> (Left addr:)) $ mkCodeBuilder' x

mkCodeBuilder' :: Code -> CodeBuilder
mkCodeBuilder' = \case
    Add  a b -> op2 0x0 a b
    Or   a b -> op2 0x1 a b
    Adc  a b -> op2 0x2 a b
    Sbb  a b -> op2 0x3 a b
    And  a b -> op2 0x4 a b
    Sub  a b -> op2 0x5 a b
    Xor  a b -> op2 0x6 a b
    Cmp  a b -> op2 0x7 a b

    Rol a b -> shiftOp 0x0 a b
    Ror a b -> shiftOp 0x1 a b
    Rcl a b -> shiftOp 0x2 a b
    Rcr a b -> shiftOp 0x3 a b
    Shl a b -> shiftOp 0x4 a b -- sal
    Shr a b -> shiftOp 0x5 a b
    Sar a b -> shiftOp 0x7 a b

    Xchg x@RegA r -> xchg_a r
    Xchg r x@RegA -> xchg_a r
    Xchg dest src -> op2' 0x43 dest' src
      where
        (dest', src') = if isMemOp src then (src, dest) else (dest, src)

    Test dest (mkImmNo64 (size dest) -> FJust (_, im)) -> case dest of
        RegA -> regprefix'' dest 0x54 mempty im
        _ -> regprefix'' dest 0x7b (reg8 0x0 dest) im
    Test dest (noImm "" -> src) -> op2' 0x42 dest' src'
      where
        (dest', src') = if isMemOp src then (src, dest) else (dest, src)

    Mov dest@(RegOp r) ((if size dest == S64 then mkImm S32 <> mkImmS S32 <> mkImmS S64 else mkImmS (size dest)) -> FJust ((se, si), im))
        | (se, si, size dest) /= (True, S32, S64) -> regprefix si dest (oneReg (0x16 .|. indicator (size dest /= S8)) r) im
        | otherwise -> regprefix'' dest 0x63 (reg8 0x0 dest) im
    Mov dest@(size -> s) (mkImmNo64 s -> FJust (_, im)) -> regprefix'' dest 0x63 (reg8 0x0 dest) im
    Mov dest src -> op2' 0x44 dest $ noImm (show (dest, src)) src

    Lea dest@(RegOp r) src | size dest /= S8 -> regprefix2 (resizeOperand' dest src) dest 0x46 $ reg8 (reg8_ r) src
      where
        resizeOperand' :: IsSize s1 => Operand s1 x -> Operand s2 RW -> Operand s1 RW
        resizeOperand' _ = resizeOperand

    Not  a -> op1 0x7b 0x2 a
    Neg  a -> op1 0x7b 0x3 a
    Inc  a -> op1 0x7f 0x0 a
    Dec  a -> op1 0x7f 0x1 a
    Call a -> op1' 0xff 0x2 a
    Jmpq a -> op1' 0xff 0x4 a

    Pop dest@(RegOp r) -> regprefix S32 dest (oneReg 0x0b r) mempty
    Pop dest -> regprefix S32 dest (codeByte 0x8f <> reg8 0x0 dest) mempty

    Push (mkImmS S8 -> FJust (_, im))  -> codeByte 0x6a <> im
    Push (mkImmS S32 -> FJust (_, im)) -> codeByte 0x68 <> im
    Push dest@(RegOp r) -> regprefix S32 dest (oneReg 0x0a r) mempty
    Push dest -> regprefix S32 dest (codeByte 0xff <> reg8 0x6 dest) mempty

    Ret   -> codeByte 0xc3
    Nop   -> codeByte 0x90
    PushF -> codeByte 0x9c
    PopF  -> codeByte 0x9d
    Cmc   -> codeByte 0xf5
    Clc   -> codeByte 0xf8
    Stc   -> codeByte 0xf9
    Cli   -> codeByte 0xfa
    Sti   -> codeByte 0xfb
    Cld   -> codeByte 0xfc
    Std   -> codeByte 0xfd

    J S8  (Condition c) -> codeByte (0x70 .|. c) <> mkRef S8 1 0
    J S32 (Condition c) -> codeByte 0x0f <> codeByte (0x80 .|. c) <> mkRef S32 4 0

    -- short jump
    Jmp -> codeByte 0xeb <> mkRef S8 1 0

    Label -> ExactCodeBuilder 0 lab
      where
        lab :: CodeBuilderState -> (CodeBuilderRes, LabelState)
        lab (n, labs) = (Right <$> concatMap g corr, labs')
          where
            (corr, labs') = replL (Right n) labs

            g (size, p, v) = zip [p..] $ getBytes $ case (size, v + n) of
                (S8, Integral v) -> toBytes (v :: Int8)
                (S32, Integral v) -> toBytes (v :: Int32)

            replL x (Left z: zs) = (z, x: zs)
            replL x (z: zs) = second (z:) $ replL x zs

    Data x -> bytesToCodeBuilder x
    Align s -> CodeBuilder $ \(n, labs) -> let
                    n' = fromIntegral $ (fromIntegral n - 1 :: Int64) .|. f s + 1
                in (Right <$> zip [n..] (replicate (n' - n) 0x90), (n', labs))
      where
        f :: Size -> Int64
        f s = sizeLen s - 1
  where
    convertImm :: Bool{-signed-} -> Size -> Operand s k -> First ((Bool, Size), CodeBuilder)
    convertImm a b (ImmOp (Immediate c)) = First $ (,) (a, b) . bytesToCodeBuilder <$> integralToBytes a b c
    convertImm True b (ImmOp (LabelRelValue s d)) | b == s = FJust $ (,) (True, b) $ mkRef s (sizeLen s) d
    convertImm _ _ _ = FNothing

    mkImmS, mkImm, mkImmNo64 :: Size -> Operand s k -> First ((Bool, Size), CodeBuilder)
    mkImmS = convertImm True
    mkImm  = convertImm False
    mkImmNo64 s = mkImmS (no64 s)

    xchg_a :: IsSize s => Operand s a -> CodeBuilder
    xchg_a dest@(RegOp r) | size dest /= S8 = regprefix (size dest) dest (oneReg 0x12 r) mempty
    xchg_a dest = regprefix'' dest 0x43 (reg8 0x0 dest) mempty

    toCode :: HasBytes a => a -> CodeBuilder
    toCode = bytesToCodeBuilder . toBytes

    sizePrefix_ :: [SReg] -> Size -> Operand s a -> Word8 -> CodeBuilder -> CodeBuilder -> CodeBuilder
    sizePrefix_ rs s r x c im
        | noHighRex rs = pre <> c <> displacement r <> im
        | otherwise = error "cannot use high register in rex instruction"
      where
        pre = case s of
            S8  -> mem32pre r <> iff (any isRex rs || x /= 0) (prefix40_ x)
            S16 -> codeByte 0x66 <> mem32pre r <> prefix40 x
            S32 -> mem32pre r <> prefix40 x
            S64 -> mem32pre r <> prefix40 (0x8 .|. x)

        mem32pre :: Operand s k -> CodeBuilder
        mem32pre (MemOp r@Addr{}) | size r == S32 = codeByte 0x67
        mem32pre _ = mempty

        prefix40 x = iff (x /= 0) $ prefix40_ x
        prefix40_ x = codeByte $ 0x40 .|. x

        displacement :: Operand s a -> CodeBuilder
        displacement RegOp{} = mempty
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

    reg8_ :: Reg t -> Word8
    reg8_ (NormalReg r) = r .&. 0x7
    reg8_ (HighReg r) = r .|. 0x4

    regprefix :: IsSize s => Size -> Operand s a -> CodeBuilder -> CodeBuilder -> CodeBuilder
    regprefix s r c im = sizePrefix_ (regs r) s r (extbits r) c im

    regprefix2 :: (IsSize s1, IsSize s) => Operand s1 a1 -> Operand s a -> Word8 -> CodeBuilder -> CodeBuilder
    regprefix2 r r' p c = sizePrefix_ (regs r <> regs r') (size r) r (extbits r' `shiftL` 2 .|. extbits r) (extension r p <> c) mempty

    regprefix'' :: IsSize s => Operand s a -> Word8 -> CodeBuilder -> CodeBuilder -> CodeBuilder
    regprefix'' r p c = regprefix (size r) r $ extension r p <> c

    extension :: HasSize a => a -> Word8 -> CodeBuilder
    extension x p = codeByte $ p `shiftL` 1 .|. indicator (size x /= S8)

    extbits :: Operand s a -> Word8
    extbits = \case
        MemOp (Addr b _ i) -> maybe 0 indexReg b .|. maybe 0 ((`shiftL` 1) . indexReg . snd) i
        RegOp r -> indexReg r
        IPMemOp{} -> 0
      where
        indexReg (NormalReg r) = r `shiftR` 3 .&. 1
        indexReg _ = 0

    reg8 :: Word8 -> Operand s a -> CodeBuilder
    reg8 w x = codeByte $ operMode x `shiftL` 6 .|. w `shiftL` 3 .|. rc x
      where
        operMode :: Operand s a -> Word8
        operMode (MemOp (Addr (Just (reg8_ -> 0x5)) NoDisp _)) = 0x1   -- [rbp] --> [rbp + 0]
        operMode (MemOp (Addr Nothing _ _)) = 0x0
        operMode (MemOp (Addr _ NoDisp _))  = 0x0
        operMode (MemOp (Addr _ (Disp (Integral (_ :: Int8))) _))  = 0x1
        operMode (MemOp (Addr _ Disp{} _))  = 0x2
        operMode IPMemOp{}                  = 0x0
        operMode RegOp{}                    = 0x3

        rc :: Operand s a -> Word8
        rc (MemOp (Addr (Just r) _ NoIndex)) = reg8_ r
        rc MemOp{}   = 0x04      -- SIB byte
        rc IPMemOp{} = 0x05
        rc (RegOp r) = reg8_ r

    op2 :: IsSize s => Word8 -> Operand s RW -> Operand s k -> CodeBuilder
    op2 op dest@RegA src@(mkImmNo64 (size dest) -> FJust (_, im)) | size dest == S8 || isNothing (getFirst $ mkImmS S8 src)
        = regprefix'' dest (op `shiftL` 2 .|. 0x2) mempty im
    op2 op dest (mkImmS S8 <> mkImmNo64 (size dest) -> FJust ((_, k), im))
        = regprefix'' dest (0x40 .|. indicator (size dest /= S8 && k == S8)) (reg8 op dest) im
    op2 op dest src = op2' (op `shiftL` 2) dest $ noImm "1" src

    noImm :: String -> Operand s k -> Operand s RW
    noImm _ (RegOp r) = RegOp r
    noImm _ (MemOp a) = MemOp a
    noImm _ (IPMemOp a) = IPMemOp a
    noImm er _ = error $ "immediate value of this size is not supported: " ++ er

    op2' :: IsSize s => Word8 -> Operand s RW -> Operand s RW -> CodeBuilder
    op2' op dest src@RegOp{} = op2g op dest src
    op2' op dest@RegOp{} src = op2g (op .|. 0x1) src dest

    op2g :: (IsSize t, IsSize s) => Word8 -> Operand s a1 -> Operand t a -> CodeBuilder
    op2g op dest src@(RegOp r) = regprefix2 dest src op $ reg8 (reg8_ r) dest

    op1_ :: IsSize s => Word8 -> Word8 -> Operand s a -> CodeBuilder -> CodeBuilder
    op1_ r1 r2 dest im = regprefix'' dest r1 (reg8 r2 dest) im

    op1 :: IsSize s => Word8 -> Word8 -> Operand s a -> CodeBuilder
    op1 a b c = op1_ a b c mempty

    op1' :: Word8 -> Word8 -> Operand S64 RW -> CodeBuilder
    op1' r1 r2 dest = regprefix S32 dest (codeByte r1 <> reg8 r2 dest) mempty

    shiftOp :: IsSize s => Word8 -> Operand s RW -> Operand S8 k -> CodeBuilder
    shiftOp c dest (ImmOp (Immediate 1)) = op1 0x68 c dest
    shiftOp c dest (mkImm S8 -> FJust (_, i)) = op1_ 0x60 c dest i
    shiftOp c dest RegCl = op1 0x69 c dest
    shiftOp _ _ _ = error "invalid shift operands"

    oneReg :: Word8 -> Reg t -> CodeBuilder
    oneReg x r = codeByte $ x `shiftL` 3 .|. reg8_ r

