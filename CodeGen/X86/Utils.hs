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
import CodeGen.X86.CallConv

-------------------------------------------------------------- derived constructs

(<.>) :: Code -> Code -> Code
a <.> b = a <> Label <> b

a <:> b = Scope $ a <.> b

infixr 5 <:>, <.>

j c x = J c <> Up x <:> mempty

x `j_back` c = mempty <:> Up x <> J c

if_ c a b = (J c <> Up (Up a <> Jmp) <:> mempty) <> Up b <:> mempty

lea8 :: IsSize s => Operand s RW -> Operand S8 RW -> Code
lea8 = Lea

leaData r d = (lea8 r ipBase <> Up Jmp <:> mempty) <> Data (toBytes d) <:> mempty

------------------------------------------------------------------------------ 

foreign import ccall "static stdio.h &printf" printf :: FunPtr a

------------------------------------------------------------------------------ 
-- * utils

mov' :: forall s s' r . IsSize s' => Operand s RW -> Operand s' r -> Code
mov' a b = Mov (resizeOperand a :: Operand s' RW) b

newtype CString = CString String

instance HasBytes CString where
    toBytes (CString cs) = mconcat $ toBytes . (fromIntegral :: Int -> Word8) . fromEnum <$> (cs ++ "\0")

-- | we should implement PUSHA and POPA later
all_regs_except_rsp :: [Operand S64 rw]
all_regs_except_rsp = [ rax, rcx, rdx, rbx, {- rsp, -} rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15 ]

push_all = mconcat [ Push r | r <-         all_regs_except_rsp ]
pop_all  = mconcat [ Pop  r | r <- reverse all_regs_except_rsp ]

traceReg :: IsSize s => String -> Operand s RW -> Code
traceReg d r = 
       push_all
    <> mov' arg2 r <> leaData arg1 (CString $ show r ++ " = %" ++ s ++ d ++ "\n") <> Xor rax rax <> callFun r11 printf
    <> pop_all
  where
    s = case size r of
        S8  -> "hh"
        S16 -> "h"
        S32 -> ""
        S64 -> "l"

