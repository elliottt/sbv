module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do arr <- cgInputArr 2 "x"
     let bar = uninterpret "bar"
     let f [a,b] =
           let r = ite (bnot (a .> 10))
                     (((a + 32) `shiftL` 10) `shiftR` 20)
                     (abs (a - (10 :: SWord32)))
            in rotateR ((bar b + (r # r)) :: SWord64) 10

     cgReturn (f arr)
