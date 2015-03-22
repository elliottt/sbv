module Data.SBV.Examples.CodeGeneration.LLVM where

import Data.SBV


test = compileToLLVM Nothing "foo" $
  do x <- cgInput "x"
     y <- cgInput "y"

     let f :: SWord32 -> SWord32 -> SWord32
         f a b =
           let w :: SWord64
               w  = a # b

               h,l :: SWord32
               (h,l) = split w

            in snd (split (l # h))

     cgReturn (f x y)
