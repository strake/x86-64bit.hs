{-# language CPP #-}
{-# language BangPatterns #-}
{-# language NoMonomorphismRestriction #-}
{-# language ScopedTypeVariables #-}
{-# language DataKinds #-}
{-# language ForeignFunctionInterface #-}
module CodeGen.X86.Utils where

import Data.Char
import Data.Monoid
import Control.Monad
import Foreign
import System.Environment
import Debug.Trace

import CodeGen.X86.Asm
import CodeGen.X86.CodeGen
import CodeGen.X86.CallConv

-------------------------------------------------------------- derived constructs

(<.>) :: Code -> Code -> Code
a <.> b = a <> Label <> b

a <:> b = Scope $ a <.> b

infixr 5 <:>, <.>

-- | auto size conditional forward jump
j c x = if f $ mkCodeBuilder (Up x) then j8 c x else j32 c x
  where
    f (ExactCodeBuilder len _) = len <= 127
    f _ = False

-- | short conditional forward jump
j8 c x = J (Just S8) c <> Up x <:> mempty

-- | near conditional forward jump
j32 c x = J (Just S32) c <> Up x <:> mempty

-- | auto size conditional backward jump
x `j_back` c = mempty <:> Up x <> J Nothing c

-- | short conditional backward jump
x `j_back8` c = mempty <:> Up x <> J (Just S8) c

-- | near conditional backward jump
x `j_back32` c = mempty <:> Up x <> J (Just S32) c

if_ c a b = (J (Just S8) c <> Up (Up a <> Jmp) <:> mempty) <> Up b <:> mempty

lea8 :: IsSize s => Operand RW s -> Operand RW S8 -> Code
lea8 = Lea

leaData r d = (lea8 r ipBase <> Up Jmp <:> mempty) <> Data (toBytes d) <:> mempty

------------------------------------------------------------------------------ 

foreign import ccall "static stdio.h &printf" printf :: FunPtr a

------------------------------------------------------------------------------ 
-- * utils

mov' :: forall s s' r . IsSize s' => Operand RW s -> Operand r s' -> Code
mov' a b = Mov (resizeOperand a :: Operand RW s') b

newtype CString = CString String

instance HasBytes CString where
    toBytes (CString cs) = mconcat $ toBytes . (fromIntegral :: Int -> Word8) . fromEnum <$> (cs ++ "\0")

-- | we should implement PUSHA and POPA later
all_regs_except_rsp :: [Operand rw S64]
all_regs_except_rsp = [ rax, rcx, rdx, rbx, {- rsp, -} rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15 ]

push_all = mconcat [ Push r | r <-         all_regs_except_rsp ]
pop_all  = mconcat [ Pop  r | r <- reverse all_regs_except_rsp ]

traceReg :: IsSize s => String -> Operand RW s -> Code
traceReg d r = 
       PushF <> push_all
    <> mov' arg2 r <> leaData arg1 (CString $ show r ++ " = %" ++ s ++ d ++ "\n") <> Xor rax rax <> callFun r11 printf
    <> pop_all <> PopF
  where
    s = case size r of
        S8  -> "hh"
        S16 -> "h"
        S32 -> ""
        S64 -> "l"

