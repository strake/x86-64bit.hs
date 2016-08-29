module CodeGen.X86.Examples where

import Foreign

import CodeGen.X86

------------------------------------------------------------------------------ 
-- * examples

-- | Example: identity function in Assembly (look at the source code)
--
-- Input: @rdi@ on Linux \/ System V, @rcx@ on Win64
--
-- Output: @rax@
idCode
    =  Mov result arg1
    <> Ret

idFun :: Word64 -> Word64
idFun = compile idCode 

-- | Example: Fibonacci function in Assembly
fibCode = saveNonVolatile 
    $  Mov rdi arg1
    <> Inc rdi
    <> Xor rdx rdx
    <> Mov rax 1
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> Dec rdi) `j_back` NZ

fibFun :: Word64 -> Word64
fibFun = compile fibCode 

-- | Example: trace a register in Assembly
tracedFibCode = saveNonVolatile 
    $  Mov rdi arg1
    <> Inc rdi
    <> Xor rdx rdx
    <> Mov rax 1
    <> (Mov rcx rax <> Mov rax rdx <> Add rdx rcx <> traceReg "d" rax {- <> traceReg "d" rdi -} <> Dec rdi) `j_back` NZ

tracedFibFun :: Word64 -> Word64
tracedFibFun = compile tracedFibCode 

-- | Example: call Haskell @fib@ function from Assembly
callHsCode
    =  callFun r11 (hsPtr fib)
    <> Ret

fib :: Word64 -> Word64
fib n = go n 0 1
  where
    go 0 a b = b `seq` a
    go n a b = go (n-1) b (a+b)

callHsFun :: Word64 -> Word64
callHsFun = compile callHsCode 

-- | Example: call C @printf@ function from Assembly
--
callCCode name = saveNonVolatile
    $  leaData arg1 (CString "Hello %s!\n")
    <> leaData arg2 (CString name)
    <> Xor rax rax                     -- zero XMM arguments ?????
    <> callFun r11 printf

callCFun :: String -> IO ()
callCFun name = compile $ callCCode name

-------------------------------------------------------

memTestFun :: Word64 -> IO Bool
memTestFun v = do
    r <- mallocBytes 8                -- this is not required to be aligned (and in any case malloc aligns to machine words)
    pokeByteOff r 0 (v :: Word64)
    let code = saveNonVolatile 
             $ Mov rdi arg1 <> Mov rax (addr rdi)
    return $ compile code r == v


