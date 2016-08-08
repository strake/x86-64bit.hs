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

-------------------------------------------------------------- derived constructs

(<.>) :: Code -> Code -> Code
a <.> b = a <> Label <> b

a <:> b = Scope $ a <.> b

infixr 5 <:>, <.>

j c x = J c <> Up x <:> mempty

x `j_back` c = mempty <:> Up x <> J c

if_ c a b = (J c <> Up (Up a <> Jmp) <:> mempty) <> Up b <:> mempty

leaData r d = (Lea r (ipBase :: Operand S8 RW) <> Up Jmp <:> mempty) <> Data (toBytes d) <:> mempty

------------------------------------------------------------------------------ utils

-- helper to call a function
callFun :: Operand S64 RW -> FunPtr a -> Code
callFun r p = Mov r (imm $ fromIntegral $ ptrToIntPtr $ castFunPtrToPtr p) <> Call r

foreign import ccall "static stdio.h &printf" printf :: FunPtr a

mov' :: forall s s' r . IsSize s' => Operand s RW -> Operand s' r -> Code
mov' a b = Mov (resizeOperand a :: Operand s' RW) b

newtype CString = CString String

instance HasBytes CString where
    toBytes (CString cs) = mconcat $ toBytes . (fromIntegral :: Int -> Word8) . fromEnum <$> (cs ++ "\0")

traceReg :: IsSize s => String -> Operand s RW -> Code
traceReg d r = 
       Push rsi <> Push rdi <> Push rax <> Push rcx <> Push rdx
    <> mov' rsi r <> leaData rdi (CString $ show r ++ " = %" ++ s ++ d ++ "\n") <> callFun rax printf
    <> Pop rdx <> Pop rcx <> Pop rax <> Pop rdi <> Pop rsi
  where
    s = case size r of
        S8  -> "hh"
        S16 -> "h"
        S32 -> ""
        S64 -> "l"

