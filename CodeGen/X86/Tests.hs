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
{-# LANGUAGE TemplateHaskell #-}
module CodeGen.X86.Tests (runTests) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Bits
import Data.Int
import Data.Word

import Test.QuickCheck hiding ((.&.))
import Debug.Trace

import CodeGen.X86.Asm
import CodeGen.X86.CodeGen
import CodeGen.X86.FFI
import CodeGen.X86.Utils

------------------------------------------------------------------------------

class HasSigned a where
    type Signed a
    toSigned   :: a -> Signed a
    fromSigned :: Signed a -> a
    shiftMask  :: a

instance HasSigned Word8  where
    type Signed Word8  = Int8
    toSigned   = fromIntegral
    fromSigned = fromIntegral
    shiftMask  = 0x1f

instance HasSigned Word16 where
    type Signed Word16 = Int16
    toSigned   = fromIntegral
    fromSigned = fromIntegral
    shiftMask  = 0x1f

instance HasSigned Word32 where
    type Signed Word32 = Int32
    toSigned   = fromIntegral
    fromSigned = fromIntegral
    shiftMask  = 0x1f

instance HasSigned Word64 where
    type Signed Word64 = Int64
    toSigned   = fromIntegral
    fromSigned = fromIntegral
    shiftMask  = 0x3f

------------------------------------------------------------------------------

prop_integral x@(Integral y) = x == y

------------------------------------------------------------------------------

instance Arbitrary Size  where arbitrary = elements [S8, S16, S32, S64]

instance Arbitrary Scale where arbitrary = elements [s1, s2, s4, s8]

arbVal :: Size -> Gen Int64
arbVal S8  = fromIntegral <$> (arbitrary :: Gen Int8)
arbVal S16 = fromIntegral <$> (arbitrary :: Gen Int16)
arbVal S32 = fromIntegral <$> (arbitrary :: Gen Int32)
arbVal S64 = fromIntegral <$> (arbitrary :: Gen Int64)

genReg8 :: Gen (Reg S8)
genReg8 = elements ((NormalReg <$> [0..15]) ++ (HighReg <$> [0..3]))
genReg16 :: Gen (Reg S16)
genReg16 = NormalReg <$> elements [0..15]
genReg32 :: Gen (Reg S32)
genReg32 = NormalReg <$> elements [0..15]
genReg64 :: Gen (Reg S64)
genReg64 = NormalReg <$> elements [0..15]

instance IsSize s => Arbitrary (Reg s) where
    arbitrary = f (ssize :: SSize s) where
        f :: SSize s -> Gen (Reg s)
        f SSize8  = genReg8
        f SSize16 = genReg16
        f SSize32 = genReg32
        f SSize64 = genReg64

genRegs = RegOp <$> arbitrary

genIPBase = pure ipBase

instance Arbitrary (Addr S64) where
    arbitrary = suchThat (Addr <$> base <*> disp <*> index) ok
      where
        ok (Addr Nothing _ Nothing) = False
        ok (Addr Nothing _ (Just (sc, _))) = sc == s1
        ok _ = True
        base = oneof
            [ return Nothing
            , Just <$> arbitrary
            ]
        disp = oneof
            [ return NoDisp
            , Disp <$> arbitrary
            ]
        index = oneof
            [ return NoIndex
            , IndexReg <$> arbitrary <*> iregs
            ]
        iregs = NormalReg <$> elements ([0..15] \\ [4])      -- sp cannot be index

genMems = MemOp <$> (arbitrary :: Gen (Addr S64))

instance IsSize s => Arbitrary (Operand s RW) where
    arbitrary = oneof
        [ genRegs
        , genMems
        , genIPBase
        ]

instance IsSize s => Arbitrary (Operand s R) where
    arbitrary = oneof
        [ imm <$> oneof (arbVal <$> [S8, S16, S32, S64])
        , genRegs
        , genMems
        , genIPBase
        ]

instance Arbitrary Code where
    arbitrary = oneof
        [ op2 Add
        , op2 Or
        , op2 Adc
        , op2 Sbb
        , op2 And
        , op2 Sub
        , op2 Xor
        , op2 Cmp
        , op2 Test
        , op2' Rol
        , op2' Ror
        , op2' Rcl
        , op2' Rcr
        , op2' Shl
        , op2' Shr
        , op2' Sar
        , op2'' Mov
        ]
      where
        op2 :: (forall s . IsSize s => Operand s RW -> Operand s R -> Code) -> Gen Code
        op2 op = oneof
            [ f op (arbitrary :: Gen (Operand S8 RW))  arbitrary
            , f op (arbitrary :: Gen (Operand S16 RW)) arbitrary
            , f op (arbitrary :: Gen (Operand S32 RW)) arbitrary
            , f op (arbitrary :: Gen (Operand S64 RW)) arbitrary
            ]
          where
            f :: forall s . IsSize s => (Operand s RW -> Operand s R -> Code) -> Gen (Operand s RW) -> Gen (Operand s R) -> Gen Code
            f op a b = uncurry op <$> suchThat ((,) <$> a <*> b) (\(a, b) -> noHighRex (regs a <> regs b) && ok' a b && okk a b)

        op2'' :: (forall s . IsSize s => Operand s RW -> Operand s R -> Code) -> Gen Code
        op2'' op = oneof
            [ f op (arbitrary :: Gen (Operand S8 RW))  arbitrary
            , f op (arbitrary :: Gen (Operand S16 RW)) arbitrary
            , f op (arbitrary :: Gen (Operand S32 RW)) arbitrary
            , f op (arbitrary :: Gen (Operand S64 RW)) arbitrary
            ]
          where
            f :: forall s . IsSize s => (Operand s RW -> Operand s R -> Code) -> Gen (Operand s RW) -> Gen (Operand s R) -> Gen Code
            f op a b = uncurry op <$> suchThat ((,) <$> a <*> b) (\(a, b) -> noHighRex (regs a <> regs b) && ok' a b && oki a b)

        op2' :: (forall s . IsSize s => Operand s RW -> Operand S8 R -> Code) -> Gen Code
        op2' op = oneof
            [ f op (arbitrary :: Gen (Operand S8 RW))  arb
            , f op (arbitrary :: Gen (Operand S16 RW)) arb
            , f op (arbitrary :: Gen (Operand S32 RW)) arb
            , f op (arbitrary :: Gen (Operand S64 RW)) arb
            ]
          where
            arb = oneof
                [ imm <$> (arbitrary :: Gen Word8)
                , return cl
                ]

            f :: forall s . IsSize s => (Operand s RW -> Operand S8 R -> Code) -> Gen (Operand s RW) -> Gen (Operand S8 R) -> Gen Code
            f op a b = uncurry op <$> suchThat ((,) <$> a <*> b) (\(a, b) -> noHighRex (regs a <> regs b) && ok' a b && okk a b && noteqreg a b)

        noteqreg a b = x == nub x where x = map phisicalReg $ regs a ++ regs b

        okk (size -> s) (ImmOp (Immediate i)) = isJust (integralToBytes True (no64 s) i)
        okk _ _ = True

        -- TODO: remove
        ok' RegOp{} RegOp{} = True
        ok' a b | isMemOp a && isMemOp b = False
        ok' a b = noteqreg a b

        oki x@RegOp{} (ImmOp (Immediate i)) = isJust (integralToBytes True (size x) i)
        oki a b = okk a b

---------------------------------------------------

evalOp :: forall a . (HasSigned a, Integral a, Integral (Signed a), FiniteBits (Signed a), Num a, FiniteBits a) => Code -> Bool -> a -> a -> ((Bool, Bool), a)
evalOp op c = case op of
    Add{}  -> mk (+)
    Or{}   -> mk (.|.)
    Adc{}  -> mk $ if c then \a b -> a + b + 1 else (+)
    Sbb{}  -> mk $ if c then \a b -> a - b - 1 else (-)
    And{}  -> mk (.&.)
    Sub{}  -> mk (-)
    Xor{}  -> mk xor
    Cmp{}  -> mk_ (-) (\a b -> a)
    Test{} -> mk_ (.&.) (\a b -> a)
    Mov{}  -> \a b -> ((c, False), b)
    Shl{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) in ((if i == 0 then c else a `testBit` (finiteBitSize a - i), False), a `shiftL` i)
    Shr{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) in ((if i == 0 then c else a `testBit` (i-1), False), a `shiftR` i)
    Sar{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) in ((if i == 0 then c else toSigned a `testBit'` (i-1), False), fromSigned (toSigned a `shiftR` i))
    Rol{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) in ((if i == 0 then c else a `testBit` ((finiteBitSize a - i) `mod` finiteBitSize a), False), a `roL` i)
    Ror{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) in ((if i == 0 then c else a `testBit` ((i-1) `mod` finiteBitSize a), False), a `roR` i)
    Rcl{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) `mod` (finiteBitSize a + 1) in ((if i == 0 then c else a `testBit` (finiteBitSize a - i), False), rcL c a i)
    Rcr{}  -> \a b -> let i = fromIntegral (b .&. shiftMask) `mod` (finiteBitSize a + 1) in ((if i == 0 then c else a `testBit` (i-1), False), rcR c a i)

  where
    mk :: (forall b . (Num b, Bits b, Integral b) => b -> b -> b) -> a -> a -> ((Bool, Bool), a)
    mk f = mk_ f f

    mk_ :: (forall b . (Num b, Bits b, Integral b) => b -> b -> b) -> (a -> a -> a) -> a -> a -> ((Bool, Bool), a)
    mk_ f g a b = ((extend (f a b) /= f (extend a) (extend b), sextend (f a b) /= f (sextend a) (sextend b)), g a b)

    extend :: a -> Integer
    extend = fromIntegral
    sextend :: a -> Integer
    sextend = fromIntegral . toSigned

    rcL c a 0 = a
    rcL c a i = (if c then setBit else clearBit) (a `shiftL` i .|. a `shiftR` (finiteBitSize a - i + 1)) (i - 1)

    rcR c a 0 = a
    rcR c a i = (if c then setBit else clearBit) (a `shiftR` i .|. a `shiftL` (finiteBitSize a - i + 1)) (finiteBitSize a - i)

    roL a i = a `shiftL` j .|. a `shiftR` (finiteBitSize a - j)
      where
        j = i `mod` finiteBitSize a

    roR a i = a `shiftR` j .|. a `shiftL` (finiteBitSize a - j)
      where
        j = i `mod` finiteBitSize a

    testBit' a i
        | isSigned a && i >= finiteBitSize a = testBit a (finiteBitSize a - 1)
        | otherwise = testBit a i


data InstrTest = IT String Code

instance Show InstrTest where show (IT s _) = s

instance Arbitrary InstrTest where
    arbitrary = do
        i <- arbitrary
        cF <- arbitrary
        let   fff :: forall s s' r . (IsSize s, IsSize s') => Code -> (Operand s RW -> Operand s' r -> Code) -> Operand s RW -> Operand s' r -> Gen InstrTest
              fff op op' a b = do
                let
                    (f1: f2: _) = map RegOp $ filter (`notElem` (regi a ++ regi b)) $ NormalReg <$> [8..15]
                    regi = map phisicalReg . regs

                    ff :: Operand s RW -> Operand s' k -> Gen (Int64, Int64, Code -> Code)
                    ff a@(RegOp x) (RegOp x') | Just Refl <- sizeEqCheck x x', x == x' = do
                        (av, inita) <- mkVal f2 a
                        return (av, av, inita)
                    ff (MemOp (Addr (Just x) _ _)) (RegOp x') | phisicalReg (SReg x) == phisicalReg (SReg x') = error "TODO" {-do
                        (av, inita) <- mkVal a
                        return (av, av, inita) -}
                    ff a_ b_ = do
                        (av, inita) <- mkVal f2 a_
                        (bv, initb) <- mkVal f2 b_
                        return (av, bv, inita . initb)

                (av, bv, initab) <- ff a b
                let
                    code = foldMap Push sr <> Mov f1 rsp <> PushF <> Pop rax <> Push rax <> PopF
                        <> initab (initcf <> cc <> mova) <> mkRes
                        <> Mov rsp f1 {- <> traceReg "X" rdx' -} <> foldMap Pop (reverse sr) <> Ret

                    sr = [rsi, rdi, rbx, rbp, r12, r13, r14, r15]

                    cc = i
                    initcf = if cF then Stc else Clc
                    mova = case a of
                        RegOp (NormalReg 0x2) -> mempty
                        _ -> Mov rdx' a
                    mkRes = otest cc (if_ (if cF' then C else NC) (Xor rax rax) (Xor rax rax <> Mov rcx res <> Cmp rcx' rdx' <> j NZ (Inc rax)))
                    isShift = \case
                        Rol{} -> True
                        Ror{} -> True
                        Rcl{} -> True
                        Rcr{} -> True
                        Shl{} -> True
                        Shr{} -> True
                        Sar{} -> True
                        _ -> False
                    otest i x | isShift i = x
                    otest _ x = if_ (if oF' then O else NO) (Xor rax rax) x

                    rcx' = resizeOperand rcx :: Operand s RW
                    rdx' = resizeOperand rdx :: Operand s RW
                    sa = size a

                    ((cF', oF'), res) = case sa of
                        S8  -> imm <$> evalOp op cF (fromIntegral av) (fromIntegral bv :: Word8)
                        S16 -> imm <$> evalOp op cF (fromIntegral av) (fromIntegral bv :: Word16)
                        S32 -> imm <$> evalOp op cF (fromIntegral av) (fromIntegral bv :: Word32)
                        S64 -> imm <$> evalOp op cF (fromIntegral av) (fromIntegral bv :: Word64)

                    msg = unlines [show i, "code: " ++ show cc, "input a: " ++ show av, "input b: " ++ show bv, "input flags: " ++ show cF, "output: " ++ show res, "output flags: " ++ show cF' ++ " " ++ show oF']

                return $ traceShow i $ IT msg code

        case i of
            Add a_ b_ -> fff i Add a_ b_
            Or  a_ b_ -> fff i Or  a_ b_
            Adc a_ b_ -> fff i Adc a_ b_
            Sbb a_ b_ -> fff i Sbb a_ b_
            And a_ b_ -> fff i And a_ b_
            Sub a_ b_ -> fff i Sub a_ b_
            Xor a_ b_ -> fff i Xor a_ b_
            Cmp a_ b_ -> fff i Cmp a_ b_
            Test a_ b_ -> fff i Test a_ b_
            Rol a_ b_ -> fff i Rol a_ b_
            Ror a_ b_ -> fff i Ror a_ b_
            Rcl a_ b_ -> fff i Rcl a_ b_
            Rcr a_ b_ -> fff i Rcr a_ b_
            Shl a_ b_ -> fff i Shl a_ b_
            Shr a_ b_ -> fff i Shr a_ b_
            Sar a_ b_ -> fff i Sar a_ b_
            Mov a_ b_ -> fff i Mov a_ b_

      where
        mkVal :: IsSize s => Operand S64 RW -> Operand s k -> Gen (Int64, Code -> Code)
        mkVal _ o@(ImmOp (Immediate w)) = return (w, id)
        mkVal _ o@(RegOp x) = do
            v <- arbVal $ size o
            return (v, (Mov (RegOp x) (imm v) <>))
        mkVal helper x@(IPMemOp LabelRelValue{}) = do
            v <- arbVal $ size x
            return (v, \c -> Scope $ Up Jmp {- <> align (size x) -} <:> Data (toBytes v) <.> c)
        mkVal helper o@(MemOp (Addr (Just x) d i)) = do
            v <- arbVal $ size o
            (vi, setvi) <- case i of
                NoIndex -> return (0, mempty)
                IndexReg sc i -> do
                    x <- arbVal $ size i
                    return (scaleFactor sc * x, Mov (RegOp i) (imm x))
            let
                d' = (vi :: Int64) + case d of
                    NoDisp -> 0
                    Disp v -> fromIntegral v
                rx = resizeOperand $ RegOp x :: Operand S64 RW
            return (v, ((leaData rx v <> Mov helper (imm d') <> Sub rx helper <> setvi) <>))
        mkVal helper o@(MemOp (Addr Nothing d (Just (sc, x)))) = do
            v <- arbVal $ size o
            let
                d' = case d of
                    NoDisp -> 0 :: Int64
                    Disp v -> fromIntegral v
                rx = resizeOperand $ RegOp x :: Operand S64 RW
            return (v, ((leaData rx v <> Mov helper (imm d') <> Sub rx helper) <>))


propInstr (IT _ c) = compile c :: Bool

tests num = quickCheckWith stdArgs { maxSuccess = num } propInstr

-----------------------------------------

return []

-- | Run all tests
runTests = do
    $quickCheckAll
    tests 2000

