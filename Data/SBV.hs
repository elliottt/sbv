-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- (The sbv library is hosted at <http://github.com/LeventErkok/sbv>.
-- Comments, bug reports, and patches are always welcome.)
--
-- SBV: Symbolic Bit Vectors in Haskell
--
-- Express properties about bit-precise Haskell programs and automatically prove
-- them using SMT solvers.
--
-- >   $ ghci -XScopedTypeVariables
-- >   Prelude> :m Data.SBV
-- >   Prelude Data.SBV> prove $ \(x::SWord8) -> x `shiftL` 2 .== 4*x
-- >   Q.E.D.
-- >   Prelude Data.SBV> prove $ forAll ["x"] $ \(x::SWord8) -> x `shiftL` 2 .== x
-- >   Falsifiable. Counter-example:
-- >     x = 128 :: SWord8
--
-- The function 'prove' has the following type:
--
-- @
--     'prove' :: 'Provable' a => a -> 'IO' 'ThmResult'
-- @
--
-- The class 'Provable' comes with instances for n-ary predicates, for arbitrary n.
-- The predicates are just regular Haskell functions over symbolic signed and unsigned
-- bit-vectors. Functions for checking satisfiability ('sat' and 'allSat') are also
-- provided.
--
-- In particular, the sbv library introduces the types:
--
--   * 'SBool': Symbolic Booleans (bits)
--
--   * 'SWord8', 'SWord16', 'SWord32', 'SWord64': Symbolic Words (unsigned)
--
--   * 'SInt8',  'SInt16',  'SInt32',  'SInt64': Symbolic Ints (signed)
--
--   * 'SArray', 'SFunArray': Flat arrays of symbolic values
--
--   * Symbolic polynomials over GF(2^n), and polynomial arithmetic
--
-- The user can construct ordinary Haskell programs using these types, which behave
-- very similar to their concrete counterparts. In particular these types belong to the
-- standard classes 'Num', 'Bits', custom versions of 'Eq' ('EqSymbolic') 
-- and 'Ord' ('OrdSymbolic'), along with several other custom classes for simplifying
-- bit-precise programming with symbolic values. The framework takes full advantage
-- of Haskell's type inference to avoid many common mistakes.
--
-- Furthermore, predicates (i.e., functions that return 'SBool') built out of
-- these types can also be:
--
--   * proven correct via an external SMT solver (the 'prove' function)
--
--   * checked for satisfiability (the 'sat' and 'allSat' functions)
--
--   * quick-checked
--
-- If a predicate is not valid, 'prove' will return a counterexample: An
-- assignment to inputs such that the predicate fails. The 'sat' function will
-- return a satisfying assignment, if there is one. The 'allSat' function returns
-- all satisfying assignments, lazily.
--
-- The sbv library uses third-party SMT solvers via the standard SMT-Lib interface:
-- <http://goedel.cs.uiowa.edu/smtlib/>.
--
-- While the library is designed to work with any SMT-Lib compliant SMT-solver,
-- solver specific support is required for parsing counter-example/model data since
-- there is currently no agreed upon format for getting models from arbitrary SMT
-- solvers. (The SMT-Lib2 initiative will potentially address this issue in the
-- future, at which point the sbv library can be generalized as well.) Currently, we
-- only support the Yices SMT solver from SRI as far as the counter-example
-- and model generation support is concerned: <http://yices.csl.sri.com/>.
-- However, other solvers can be hooked up with relative ease.
--
-- You /should/ download and install Yices on your machine, and make sure the
-- @yices@ executable is in your path before using the sbv library, as it is the
-- current default solver. Alternatively, you can specify the location of yices
-- executable in the environment variable @SBV_YICES@ and the options to yices
-- in @SBV_YICES_OPTIONS@. (The default for the latter is '\"-m -f\"'.)

module Data.SBV (
  -- * Programming with Symbolic values
  -- ** Symbolic types
  -- *** Symbolic bit
    SBool
  -- *** Unsigned symbolic bit-vectors
  , SWord8, SWord16, SWord32, SWord64
  -- *** Signed symbolic bit-vectors
  , SInt8, SInt16, SInt32, SInt64
  -- *** Arrays of symbolic values
  , SymArray(..), SArray, SFunArray
  -- ** Conditionals: Mergeable values
  , Mergeable(..)
  -- ** Symbolic equality
  , EqSymbolic(..)
  -- ** Symbolic ordering
  , OrdSymbolic(..)
  -- ** Division
  , BVDivisible(..)
  -- ** The Boolean class
  , Boolean(..)
  -- *** Generalizations of boolean operations
  , bAnd, bOr, bAny, bAll
  -- ** Operations on symbolic words
  -- *** Word level
  , bitValue, setBitTo, oneIf, lsb, msb
  -- *** List level
  , allEqual, allDifferent
  -- *** Blasting/Unblasting
  , blastBE, blastLE, FromBits(..)
  -- *** Splitting, joining, and extending
  , Splittable(..)
  -- ** Polynomial arithmetic
  , Polynomial(..)
  -- ** Pretty-printing and reading numbers in Hex & Binary
  , PrettyNum(..), readBin
  -- * Proving properties
  , module Data.SBV.Provers.Prover
  -- * Internals (for developers only)
  , output, Result, Symbolic, runSymbolic, SymWord(..), SBV(..)
  -- * Module exports
  , module Data.Bits
  , module Data.Word
  , module Data.Int
  ) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.BitVectors.Polynomial
import Data.SBV.BitVectors.Splittable
import Data.SBV.Provers.Prover
import Data.SBV.Utils.Boolean
import Data.Bits
import Data.Word
import Data.Int
