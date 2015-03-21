module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do x <- cgInput "x"
     let f a = ite (bnot (a .> 10))
                   (a + 10)
                   (abs (a - (10 :: SFloat)))
     cgReturn (f x)
