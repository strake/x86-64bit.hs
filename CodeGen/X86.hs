{-# language PatternSynonyms #-}
module CodeGen.X86
    (
    -- * Byte sequences
      Bytes (..)
    , HasBytes (..)
    -- * Sizes (in bits)
    , Size (..)
    , HasSize (..)
    , IsSize
    -- * Addresses
    , base
    , disp
    , index1, index2, index4, index8
    -- * Operands
    , Access (..)
    , Operand
    , resizeOperand
    -- ** Immediate values
    , imm
    -- ** Memory references
    , addr
    , ipBase
    -- ** Registers
    -- *** 64 bit registers
    , rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
    -- *** 32 bit registers
    , eax, ecx, edx, ebx, esp, ebp, esi, edi, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d
    -- *** 16 bit registers
    , ax, cx, dx, bx, sp, bp, si, di, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w
    -- *** 8 bit low registers
    , al, cl, dl, bl, spl, bpl, sil, dil, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b
    -- *** 8 bit high registers
    , ah, ch, dh, bh
    -- * Conditions
    , Condition
    , pattern O, pattern NO, pattern C, pattern NC, pattern Z, pattern NZ, pattern BE, pattern NBE, pattern S, pattern NS, pattern P, pattern NP, pattern L, pattern NL, pattern LE, pattern NLE
    -- * Assembly codes
    , Code (..)
    -- * Compound assembly codes
    , (<>)
    , (<.>), (<:>)
    , j, j_back, if_
    , lea8
    , leaData
    -- * Compilation
    , Callable
    , compile
    -- * Calling C and Haskell from Assembly
    , callFun
    , saveNonVolatile
    , arg1, arg2, arg3, arg4
    , result
    , CallableHs
    , hsPtr
    -- * Misc
    , runTests
    , CString (..)
    , traceReg
    , printf
    ) where

import Data.Monoid

import CodeGen.X86.Asm
import CodeGen.X86.CodeGen
import CodeGen.X86.FFI
import CodeGen.X86.CallConv
import CodeGen.X86.Utils
import CodeGen.X86.Tests

