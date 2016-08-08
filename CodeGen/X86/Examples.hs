{-# language BangPatterns #-}
{-# language NoMonomorphismRestriction #-}
{-# language ScopedTypeVariables #-}
{-# language DataKinds #-}
module CodeGen.X86.Examples where

import Data.Char
import Data.Monoid
import Control.Monad
import Foreign
import System.Environment
import Debug.Trace

import CodeGen.X86

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

------------------------------------------------------------------------------ examples

idCode
    =  Mov rax rdi
    <> Ret

idFun :: Word64 -> Word64
idFun = compile idCode 

fibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (imm 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> Dec rdi) `j_back` NZ
    <> Ret

fibFun :: Word64 -> Word64
fibFun = compile fibCode 

tracedFibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (imm 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> traceReg "d" rax <> Dec rdi) `j_back` NZ
    <> Ret

tracedFibFun :: Word64 -> Word64
tracedFibFun = compile tracedFibCode 

callHsCode
    =  callFun rdx (hsPtr fib)
    <> Ret

fib :: Word64 -> Word64
fib n = go n 0 1
  where
    go 0 !a !b = a
    go n a b = go (n-1) b (a+b)

callHsFun :: Word64 -> Word64
callHsFun = compile callHsCode 

callCCode name
    =  leaData rdi (CString "Hello %s!\n")
    <> leaData rsi (CString name)
    <> callFun rdx printf
    <> Ret

callCFun :: String -> IO ()
callCFun name = compile $ callCCode name

memTestFun :: Word64 -> IO Bool
memTestFun v = do
    r <- memalign 8 8
    pokeByteOff r 0 (v :: Word64)
    return $ compile (Mov rax (MemOp $ base rdi) <> Ret) r == v

