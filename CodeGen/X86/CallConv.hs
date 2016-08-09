
-- | Calling conventions. There are basically only two: System V (Linux, OSX, BSD) and Win64\/fastcall

{-# language CPP #-}
{-# language BangPatterns #-}
{-# language DataKinds #-}
module CodeGen.X86.CallConv where

import Foreign
import Data.Monoid
import CodeGen.X86.Asm

------------------------------------------------------------------------------ 

#if defined (mingw32_HOST_OS) || defined (mingw64_HOST_OS)

-- On Win64 the caller have to reserve 32 byte "shadow space" on the stack (and clean up after)
callFun :: Operand S64 RW -> FunPtr a -> Code
callFun r p 
  =  Sub rsp (imm 32) 
  <> Mov r (imm $ fromIntegral $ ptrToIntPtr $ castFunPtrToPtr p) 
  <> Call r 
  <> Add rsp (imm 32)

#else

-- helper to call a function
callFun :: Operand S64 RW -> FunPtr a -> Code
callFun r p = Mov r (imm $ fromIntegral $ ptrToIntPtr $ castFunPtrToPtr p) <> Call r

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

#elif defined (linux_HOST_OS)

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

