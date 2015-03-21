module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do x <- cgInput "x"
     let bar = uninterpret "bar"
     let f a =
           let r = ite (bnot (a .> 10))
                     (((a + 32) `shiftL` 10) `shiftR` 20)
                     (abs (a - (10 :: SWord32)))
            in (bar r + (r # r)) :: SWord64

     cgReturn (f x)
