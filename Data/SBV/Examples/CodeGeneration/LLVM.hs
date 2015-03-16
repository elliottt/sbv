module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do x <- cgInput "x"
     let f a = a + (1 :: SWord8)
     cgReturn (f x)
