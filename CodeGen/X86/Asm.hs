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
module CodeGen.X86.Asm where

import Numeric
import Data.List
import Data.Bits
import Data.Int
import Data.Word
import Control.Monad
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

------------------------------------------------------- utils

everyNth n [] = []
everyNth n xs = take n xs: everyNth n (drop n xs)

showNibble :: (Integral a, Bits a) => Int -> a -> Char
showNibble n x = toEnum (b + if b < 10 then 48 else 87)
  where
    b = fromIntegral $ x `shiftR` (4*n) .&. 0x0f

showByte b = [showNibble 1 b, showNibble 0 b]

showHex' x = "0x" ++ showHex x ""

------------------------------------------------------- byte sequences

newtype Bytes = Bytes {getBytes :: [Word8]}
    deriving (Eq, Monoid)

instance Show Bytes where
    show (Bytes ws) = unwords $ map (concatMap showByte) $ everyNth 4 ws

showBytes (Bytes ws) = unlines $ zipWith showLine [0 ::Int ..] $ everyNth 16 ws
  where
    showLine n bs = [showNibble 2 n, showNibble 1 n, showNibble 0 n, '0', ' ', ' '] ++ show (Bytes bs)

bytesCount (Bytes x) = length x

class HasBytes a where toBytes :: a -> Bytes

instance HasBytes Word8  where toBytes w = Bytes [w]
instance HasBytes Word16 where toBytes w = Bytes [fromIntegral w, fromIntegral $ w `shiftR` 8]
instance HasBytes Word32 where toBytes w = Bytes [fromIntegral $ w `shiftR` n | n <- [0, 8.. 24]]
instance HasBytes Word64 where toBytes w = Bytes [fromIntegral $ w `shiftR` n | n <- [0, 8.. 56]]

instance HasBytes Int8  where toBytes w = toBytes (fromIntegral w :: Word8)
instance HasBytes Int16 where toBytes w = toBytes (fromIntegral w :: Word16)
instance HasBytes Int32 where toBytes w = toBytes (fromIntegral w :: Word32)
instance HasBytes Int64 where toBytes w = toBytes (fromIntegral w :: Word64)

------------------------------------------------------- sizes

data Size = S8 | S16 | S32 | S64
    deriving (Eq, Ord)

instance Show Size where
    show = \case
        S8  -> "byte"
        S16 -> "word"
        S32 -> "dword"
        S64 -> "qword"

mkSize 1 = S8
mkSize 2 = S16
mkSize 4 = S32
mkSize 8 = S64

sizeLen = \case
    S8  -> 1
    S16 -> 2
    S32 -> 4
    S64 -> 8

class HasSize a where size :: a -> Size

instance HasSize Word8  where size _ = S8
instance HasSize Word16 where size _ = S16
instance HasSize Word32 where size _ = S32
instance HasSize Word64 where size _ = S64
instance HasSize Int8   where size _ = S8
instance HasSize Int16  where size _ = S16
instance HasSize Int32  where size _ = S32
instance HasSize Int64  where size _ = S64

-- | Singleton type for size
data SSize (s :: Size) where
    SSize8  :: SSize S8
    SSize16 :: SSize S16
    SSize32 :: SSize S32
    SSize64 :: SSize S64

instance HasSize (SSize s) where
    size = \case
        SSize8  -> S8
        SSize16 -> S16
        SSize32 -> S32
        SSize64 -> S64

class IsSize (s :: Size) where
    ssize :: SSize s

instance IsSize S8  where ssize = SSize8
instance IsSize S16 where ssize = SSize16
instance IsSize S32 where ssize = SSize32
instance IsSize S64 where ssize = SSize64

data EqT s s' where
    Refl :: EqT s s

sizeEqCheck :: forall s s' f g . (IsSize s, IsSize s') => f s -> g s' -> Maybe (EqT s s')
sizeEqCheck _ _ = case (ssize :: SSize s, ssize :: SSize s') of
    (SSize8 , SSize8)  -> Just Refl
    (SSize16, SSize16) -> Just Refl
    (SSize32, SSize32) -> Just Refl
    (SSize64, SSize64) -> Just Refl
    _ -> Nothing

------------------------------------------------------- scale

-- replace with Size?
newtype Scale = Scale Word8
    deriving (Eq)

s1 = Scale 0x0
s2 = Scale 0x1
s4 = Scale 0x2
s8 = Scale 0x3

scaleFactor (Scale i) = case i of
    0x0 -> 1
    0x1 -> 2
    0x2 -> 4
    0x3 -> 8

------------------------------------------------------- operand

data Operand :: Size -> Access -> * where
    ImmOp     :: Int64 -> Operand s R
    RegOp     :: Reg s -> Operand s rw
    MemOp     :: IsSize s' => Addr s' -> Operand s rw
    IPMemOp   :: Immediate Int32 -> Operand s rw

addr = MemOp

data Immediate a
    = Immediate a
    | LabelRelAddr !LabelIndex

type LabelIndex = Int

-- | Operand access modes
data Access
    = R     -- ^ readable operand
    | RW    -- ^ readable and writeable operand

data Reg :: Size -> * where
    NormalReg :: Word8 -> Reg s
    HighReg   :: Word8 -> Reg S8

data Addr s = Addr
    { baseReg        :: BaseReg s
    , displacement   :: Displacement
    , indexReg       :: IndexReg s
    }

type BaseReg s    = Maybe (Reg s)
type IndexReg s   = Maybe (Scale, Reg s)
type Displacement = Maybe Int32

pattern NoDisp = Nothing
pattern Disp a = Just a

pattern NoIndex = Nothing
pattern IndexReg a b = Just (a, b)

ipBase = IPMemOp $ LabelRelAddr 0

instance Eq (Reg s) where
    NormalReg a == NormalReg b = a == b
    HighReg a == HighReg b = a == b
    _ == _ = False

instance IsSize s => Show (Reg s) where
    show = \case
        HighReg i -> (["ah"," ch", "dh", "bh"] ++ repeat err) !! fromIntegral i
        r@(NormalReg i) -> (!! fromIntegral i) . (++ repeat err) $ case size r of
            S8  -> ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"] ++ map (++ "b") r8
            S16 -> r0 ++ map (++ "w") r8
            S32 -> map ('e':) r0 ++ map (++ "d") r8
            S64 -> map ('r':) r0 ++ r8
          where
            r0 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"]
            r8 = ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
      where
        err = error $ "show @ RegOp" -- ++ show (s, i)

instance IsSize s => Show (Addr s) where
    show (Addr b d i) = showSum $ shb b ++ shd d ++ shi i
      where
        shb Nothing = []
        shb (Just x) = [(True, show x)]
        shd NoDisp = []
        shd (Disp x) = [(signum x /= (-1), show (abs x))]
        shi NoIndex = []
        shi (IndexReg sc x) = [(True, show' (scaleFactor sc) ++ show x)]
        show' 1 = ""
        show' n = show n ++ " * "
        showSum [] = "0"
        showSum ((True, x): xs) = x ++ g xs
        showSum ((False, x): xs) = "-" ++ x ++ g xs
        g = concatMap (\(a, b) -> f a ++ b)
        f True = " + "
        f False = " - "

instance IsSize s => Show (Operand s a) where
    show = showOperand show

showOperand mklab = \case
    ImmOp w -> show w
    RegOp r -> show r
    r@(MemOp a) -> show (size r) ++ " [" ++ show a ++ "]"
    r@(IPMemOp (Immediate x)) -> show (size r) ++ " [" ++ "rel " ++ show x ++ "]"
    r@(IPMemOp (LabelRelAddr x)) -> show (size r) ++ " [" ++ "rel " ++ mklab x ++ "]"
  where
    showp x | x < 0 = " - " ++ show (-x)
    showp x = " + " ++ show x

instance IsSize s => HasSize (Operand s a) where
    size _ = size (ssize :: SSize s)

instance IsSize s => HasSize (Addr s) where
    size _ = size (ssize :: SSize s)

instance IsSize s => HasSize (BaseReg s) where
    size _ = size (ssize :: SSize s)

instance IsSize s => HasSize (Reg s) where
    size _ = size (ssize :: SSize s)

instance IsSize s => HasSize (IndexReg s) where
    size _ = size (ssize :: SSize s)

imm :: Integral a => a -> Operand s R
imm = ImmOp . fromIntegral

instance Monoid (Addr s) where
    mempty = Addr (getFirst mempty) (getFirst mempty) (getFirst mempty)
    Addr a b c `mappend` Addr a' b' c' = Addr (getFirst $ First a <> First a') (getFirst $ First b <> First b') (getFirst $ First c <> First c')

instance Monoid (IndexReg s) where
    mempty = NoIndex
    i `mappend` NoIndex = i
    NoIndex `mappend` i = i

base :: Operand s RW -> Addr s
base (RegOp x) = Addr (Just x) NoDisp NoIndex

index :: Scale -> Operand s RW -> Addr s
index sc (RegOp x) = Addr Nothing NoDisp (IndexReg sc x)

index1 = index s1
index2 = index s2
index4 = index s4
index8 = index s8

disp :: Int32 -> Addr s
disp x = Addr Nothing (Disp x) NoIndex

reg = RegOp . NormalReg

rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15 :: Operand S64 rw
rax  = reg 0x0
rcx  = reg 0x1
rdx  = reg 0x2
rbx  = reg 0x3
rsp  = reg 0x4
rbp  = reg 0x5
rsi  = reg 0x6
rdi  = reg 0x7
r8   = reg 0x8
r9   = reg 0x9
r10  = reg 0xa
r11  = reg 0xb
r12  = reg 0xc
r13  = reg 0xd
r14  = reg 0xe
r15  = reg 0xf

eax, ecx, edx, ebx, esp, ebp, esi, edi, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d :: Operand S32 rw
eax  = reg 0x0
ecx  = reg 0x1
edx  = reg 0x2
ebx  = reg 0x3
esp  = reg 0x4
ebp  = reg 0x5
esi  = reg 0x6
edi  = reg 0x7
r8d  = reg 0x8
r9d  = reg 0x9
r10d = reg 0xa
r11d = reg 0xb
r12d = reg 0xc
r13d = reg 0xd
r14d = reg 0xe
r15d = reg 0xf

ax, cx, dx, bx, sp, bp, si, di, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w :: Operand S16 rw
ax   = reg 0x0
cx   = reg 0x1
dx   = reg 0x2
bx   = reg 0x3
sp   = reg 0x4
bp   = reg 0x5
si   = reg 0x6
di   = reg 0x7
r8w  = reg 0x8
r9w  = reg 0x9
r10w = reg 0xa
r11w = reg 0xb
r12w = reg 0xc
r13w = reg 0xd
r14w = reg 0xe
r15w = reg 0xf

al, cl, dl, bl, spl, bpl, sil, dil, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b :: Operand S8 rw
al   = reg 0x0
cl   = reg 0x1
dl   = reg 0x2
bl   = reg 0x3
spl  = reg 0x4
bpl  = reg 0x5
sil  = reg 0x6
dil  = reg 0x7
r8b  = reg 0x8
r9b  = reg 0x9
r10b = reg 0xa
r11b = reg 0xb
r12b = reg 0xc
r13b = reg 0xd
r14b = reg 0xe
r15b = reg 0xf

ah   = RegOp $ HighReg 0x0
ch   = RegOp $ HighReg 0x1
dh   = RegOp $ HighReg 0x2
bh   = RegOp $ HighReg 0x3

pattern RegA = RegOp (NormalReg 0x0)

pattern RegCl :: Operand S8 r
pattern RegCl = RegOp (NormalReg 0x1)

--------------------------------------------------------------

resizeOperand :: IsSize s' => Operand s RW -> Operand s' RW
resizeOperand (RegOp x) = RegOp $ resizeRegCode x
resizeOperand (MemOp a) = MemOp a
resizeOperand (IPMemOp a) = IPMemOp a

resizeRegCode :: Reg s -> Reg s'
resizeRegCode (NormalReg i) = NormalReg i

pattern MemLike <- (isMemOp -> True)

isMemOp MemOp{} = True
isMemOp IPMemOp{} = True
isMemOp _ = False

-------------------------------------------------------------- condition

newtype Condition = Condition Word8

pattern O   = Condition 0x0
pattern NO  = Condition 0x1
pattern C   = Condition 0x2      -- b
pattern NC  = Condition 0x3      -- nb
pattern Z   = Condition 0x4      -- e
pattern NZ  = Condition 0x5      -- ne
pattern BE  = Condition 0x6      -- na
pattern NBE = Condition 0x7      -- a
pattern S   = Condition 0x8
pattern NS  = Condition 0x9
pattern P   = Condition 0xa
pattern NP  = Condition 0xb
pattern L   = Condition 0xc
pattern NL  = Condition 0xd
pattern LE  = Condition 0xe      -- ng
pattern NLE = Condition 0xf      -- g

instance Show Condition where
    show (Condition x) = case x of
        0x0 -> "o"
        0x1 -> "no"
        0x2 -> "c"
        0x3 -> "nc"
        0x4 -> "z"
        0x5 -> "nz"
        0x6 -> "be"
        0x7 -> "nbe"
        0x8 -> "s"
        0x9 -> "ns"
        0xa -> "p"
        0xb -> "np"
        0xc -> "l"
        0xd -> "nl"
        0xe -> "le"
        0xf -> "nle"

-------------------------------------------------------------- asm code

data Code where
    Ret, Nop, PushF, PopF, Cmc, Clc, Stc, Cli, Sti, Cld, Std   :: Code

    Inc, Dec, Not, Neg                                :: IsSize s => Operand s RW -> Code
    Add, Or, Adc, Sbb, And, Sub, Xor, Cmp, Test, Mov  :: IsSize s => Operand s RW -> Operand s  r -> Code
    Rol, Ror, Rcl, Rcr, Shl, Shr, Sar                 :: IsSize s => Operand s RW -> Operand S8 r -> Code

    Xchg :: IsSize s => Operand s RW -> Operand s RW -> Code
    Lea  :: (IsSize s, IsSize s') => Operand s RW -> Operand s' RW -> Code

    Pop  :: Operand S64 RW -> Code
    Push :: Operand S64 r  -> Code

    Call :: Operand S64 RW -> Code
    Jmpq :: Operand S64 RW -> Code

    J    :: Condition -> Code
    Jmp  :: Code

    Label :: Code
    Scope :: Code -> Code
    Up    :: Code -> Code

    Data  :: Bytes -> Code
    Align :: Size  -> Code

    EmptyCode  :: Code
    AppendCode :: Code -> Code -> Code

instance Monoid Code where
    mempty  = EmptyCode
    mappend = AppendCode

-------------

showCode = \case
    EmptyCode  -> return ()
    AppendCode a b -> showCode a >> showCode b

    Scope c -> get >>= \i -> put (i+1) >> local (i:) (showCode c)

    Up c -> local tail $ showCode c

    J cc  -> getLabel 0 >>= \l -> showOp ("j" ++ show cc) l
    Jmp   -> getLabel 0 >>= \l -> showOp "jmp" l
    Label -> getLabel 0 >>= codeLine

    x -> showCodeFrag x

getLabel i = ($ i) <$> getLabels

getLabels = f <$> ask
  where
    f xs i = case drop i xs of
        [] -> ".l?"
        (i: _) -> ".l" ++ show i

codeLine x = tell [x]

showCodeFrag = \case
    Add  op1 op2 -> showOp2 "add"  op1 op2
    Or   op1 op2 -> showOp2 "or"   op1 op2
    Adc  op1 op2 -> showOp2 "adc"  op1 op2
    Sbb  op1 op2 -> showOp2 "sbb"  op1 op2
    And  op1 op2 -> showOp2 "and"  op1 op2
    Sub  op1 op2 -> showOp2 "sub"  op1 op2
    Xor  op1 op2 -> showOp2 "xor"  op1 op2
    Cmp  op1 op2 -> showOp2 "cmp"  op1 op2
    Test op1 op2 -> showOp2 "test" op1 op2
    Rol  op1 op2 -> showOp2 "rol"  op1 op2
    Ror  op1 op2 -> showOp2 "rol"  op1 op2
    Rcl  op1 op2 -> showOp2 "rol"  op1 op2
    Rcr  op1 op2 -> showOp2 "rol"  op1 op2
    Shl  op1 op2 -> showOp2 "rol"  op1 op2
    Shr  op1 op2 -> showOp2 "rol"  op1 op2
    Sar  op1 op2 -> showOp2 "rol"  op1 op2
    Mov  op1 op2 -> showOp2 "mov"  op1 op2
    Lea  op1 op2 -> showOp2 "lea"  op1 op2
    Xchg op1 op2 -> showOp2 "xchg" op1 op2
    Inc  op -> showOp1 "inc"  op
    Dec  op -> showOp1 "dec"  op
    Not  op -> showOp1 "not"  op
    Neg  op -> showOp1 "neg"  op
    Pop  op -> showOp1 "pop"  op
    Push op -> showOp1 "push" op
    Call op -> showOp1 "call" op
    Jmpq op -> showOp1 "jmp"  op
    Ret   -> showOp0 "ret"
    Nop   -> showOp0 "nop"
    PushF -> showOp0 "pushf"
    PopF  -> showOp0 "popf"
    Cmc   -> showOp0 "cmc"
    Clc   -> showOp0 "clc"
    Stc   -> showOp0 "stc"
    Cli   -> showOp0 "cli"
    Sti   -> showOp0 "sti"
    Cld   -> showOp0 "cld"
    Std   -> showOp0 "std"

    Align s -> codeLine $ ".align " ++ show s
    Data (Bytes x) -> showOp "db" $ intercalate ", " (showByte <$> x) ++ "  ; " ++ show (toEnum . fromIntegral <$> x :: String)

showOp0 s = codeLine s
showOp s a = showOp0 $ s ++ " " ++ a
showOp1 s a = getLabels >>= \f -> showOp s $ showOperand f a
showOp2 s a b = getLabels >>= \f -> showOp s $ showOperand f a ++ ", " ++ showOperand f b

