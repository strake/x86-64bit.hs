-- | Calling conventions. There are basically only two: System V (Linux, OSX, BSD) and Win64\/fastcall

{-# language NoMonomorphismRestriction #-}
{-# language CPP #-}
{-# language BangPatterns #-}
{-# language DataKinds #-}
module CodeGen.X86.CallConv where

import Foreign
import Data.Monoid

import CodeGen.X86.Asm
import CodeGen.X86.CodeGen

------------------------------------------------------------------------------ 

#if defined (mingw32_HOST_OS) || defined (mingw64_HOST_OS)

-- On Win64 the caller have to reserve 32 byte "shadow space" on the stack (and clean up after)
callFun :: Operand RW S64 -> FunPtr a -> Code
callFun r p 
  =  Sub rsp 32
  <> Mov r (imm $ ptrToIntPtr $ castFunPtrToPtr p)
  <> Call r 
  <> Add rsp 32

#elif defined (darwin_HOST_OS)

-- OSX requires 16 byte alignment of the stack...
callFun :: Operand RW S64 -> FunPtr a -> Code
callFun r p 
  =  Push r15              -- we will use r15 (non-volatile) to store old rsp
  <> Mov r15 15            -- 0xf
  <> Not r15               -- 0xffff ... fff0
  <> And r15 rsp           -- align rsp into r15
  <> Xchg r15 rsp          -- new rsp = aligned, r15 = old rsp
  <> Mov r (imm $ ptrToIntPtr $ castFunPtrToPtr p)
  <> Call r 
  <> Mov rsp r15           -- restore rsp
  <> Pop r15               -- restore r15

#else

-- helper to call a function
callFun :: Operand RW S64 -> FunPtr a -> Code
callFun r p 
  =  Mov r (imm $ ptrToIntPtr $ castFunPtrToPtr p)
  <> Call r

#endif

------------------------------------------------------------------------------ 

-- | Save the non-volatile registers 
--
-- Note: R12..R15 should be preserved on both Windows and Linux.
-- This is the responsability of the user (this won't save them).
--
saveNonVolatile :: Code -> Code
saveNonVolatile code = prologue <> code <> epilogue <> Ret

------------------------------------------------------------------------------ 
-- calling conventions

#if defined (mingw32_HOST_OS) || defined (mingw64_HOST_OS)

---------- Win64 calling convention ----------

arg1 = rcx
arg2 = rdx
arg3 = r8
arg4 = r9
-- rest of the arguments on the stack

result = rax

prologue 
    =  Push rbp
    <> Push rbx
    <> Push rdi
    <> Push rsi

epilogue
    =  Pop rsi
    <> Pop rdi
    <> Pop rbx
    <> Pop rbp 

#else

---------- System V calling convention ----------

arg1 = rdi
arg2 = rsi
arg3 = rdx
arg4 = rcx
arg5 = r8
arg6 = r9
-- rest of the arguments on the stack

result = rax

prologue 
    =  Push rbp
    <> Push rbx

epilogue
    =  Pop rbx
    <> Pop rbp  

#endif

------------------------------------------------------------------------------ 

