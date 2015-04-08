module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


testC = compileToC Nothing "foo" test

testLLVM = compileToLLVM Nothing "foo" test

test =
  do x <- cgInput "x"
     y <- cgInput "y"

     let f :: SWord32 -> SWord32 -> SWord32
         f a b =
           let w :: SWord64
               w  = a # b

               h,l :: SWord32
               (h,l) = split w

            in select [h,l]   (0 :: SWord32) (ite (h .> l) 0 (1 :: SWord8))
             + select [1,2,3] (0 :: SWord32) (ite (h .> l) 0 (2 :: SWord8))

     cgReturn (f x y)
