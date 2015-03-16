module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do x <- cgInput "x"
     let f a = ite (a .> 10) (a + 10) (a - (10 :: SWord8))
     cgReturn (f x)
