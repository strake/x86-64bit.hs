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

import Data.Char
import Data.Monoid
import qualified Data.ByteString.Lazy as BS
import Control.Monad
import Foreign
import System.Environment
import Debug.Trace

import CodeGen.X86
import CodeGen.X86.Tests

------------------------------------------------------------------------------ utils

-- helper to call a function
callFun :: Operand S64 RW -> FunPtr a -> Code
callFun r p = Mov r (ImmOp $ fromIntegral $ ptrToIntPtr $ castFunPtrToPtr p) <> Call r

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

pattern Show :: (Show a, Read a) => a -> String
pattern Show x <- (maybeRead -> Just x)
  where Show x =  show x

maybeRead x = case reads x of
    ((y, cs): _) | all isSpace cs -> Just y
    _ -> Nothing

------------------------------------------------------------------------------ examples

main = do
    args <- getArgs
    case args of

        ["id", Show n] -> do
            print idCode
            print $ (compile idCode :: Word64 -> Word64) n

        ["fib", Show n] -> do
            print fibCode
            print $ (compile fibCode :: Word64 -> Word64) n

        ["fib", "traced", Show n] -> do
            print tracedFibCode
            print $ (compile tracedFibCode :: Word64 -> Word64) n

        -- for time comparison
        ["hsfib", Show n] -> print $ fib n

        ["callhs", Show n] -> do
            print callHsCode
            print $ (compile $ callHsCode :: Word64 -> Word64) n

        ["callc", name] -> do
            print $ callCCode name
            compile $ callCCode name

        ["memtest", Show v] -> do
            r <- memalign 8 8
            pokeByteOff r 0 (v :: Word64)
            print $ compile (Mov rax (MemOp $ base rdi) <> Ret) r == v

        ["tests"] -> do
            tests
            runTests
            return ()

        ["fib", "writebytes"]
            -> BS.writeFile "fib.bytes" $ BS.pack $ getBytes $ codeBytes fibCode

        _ -> putStrLn "wrong command line arguments"

idCode
    =  Mov rax rdi
    <> Ret

fibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (ImmOp 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> Dec rdi) `j_back` NZ
    <> Ret

tracedFibCode
    =  Inc rdi
    <> Xor rdx rdx
    <> Mov rax (ImmOp 1)
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> traceReg "d" rax <> Dec rdi) `j_back` NZ
    <> Ret

callHsCode
    =  callFun rdx (hsPtr fib)
    <> Ret

callCCode name
    =  leaData rdi (CString "Hello %s!\n")
    <> leaData rsi (CString name)
    <> callFun rdx printf
    <> Ret

fib :: Word64 -> Word64
fib n = go n 0 1
  where
    go 0 !a !b = a
    go n a b = go (n-1) b (a+b)

