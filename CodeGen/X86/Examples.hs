{-# language BangPatterns #-}
{-# language NoMonomorphismRestriction #-}
{-# language ScopedTypeVariables #-}
{-# language DataKinds #-}
module CodeGen.X86.Examples where

import Data.Char
import Data.Monoid
import Control.Monad
import Foreign

import CodeGen.X86

------------------------------------------------------------------------------ examples

-- | Example: identity function in Assembly (look at the source code)
--
-- Input: @rdi@
--
-- Output: @rax@
idCode
    =  Mov rax rdi
    <> Ret

idFun :: Word64 -> Word64
idFun = compile idCode 

-- | Example: Fibonacci function in Assembly
fibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (imm 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> Dec rdi) `j_back` NZ
    <> Ret

fibFun :: Word64 -> Word64
fibFun = compile fibCode 

-- | Example: trace a register in Assembly
tracedFibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (imm 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> traceReg "d" rax <> Dec rdi) `j_back` NZ
    <> Ret

tracedFibFun :: Word64 -> Word64
tracedFibFun = compile tracedFibCode 

-- | Example: call Haskell @fib@ function from Assembly
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

-- | Example: call C @printf@ function from Assembly
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
    return $ compile (Mov rax (addr $ base rdi) <> Ret) r == v

