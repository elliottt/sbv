{-# LANGUAGE RecordWildCards #-}

module Data.SBV.Compilers.LLVM where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex, showCFloat, showCDouble)
import Data.SBV.Compilers.CodeGen

import qualified Data.Foldable as F
import qualified Data.Sequence as Seq
import           Data.String (IsString(..))
import           System.Random (randoms,newStdGen)
import           Text.LLVM hiding (Result,And,Or)
import           Text.PrettyPrint.HughesPJ (render)


---------------------------------------------------------------------------
-- * API
---------------------------------------------------------------------------

compileToLLVM :: Maybe FilePath -> String -> SBVCodeGen () -> IO ()
compileToLLVM mbDirName nm f =
  compileToLLVM' nm f >>= renderCgPgmBundle mbDirName

-- | Given a symbolic computation, render it as an LLVM function definition.
compileToLLVM' :: String -> SBVCodeGen () -> IO CgPgmBundle
compileToLLVM' nm f =
  do rands <- randoms `fmap` newStdGen
     codeGen SBVToLLVM (defaultCgConfig { cgDriverVals = rands }) nm f


---------------------------------------------------------------------------
-- * Implementation
---------------------------------------------------------------------------

-- Unexpected input, or things we will probably never support
die :: String -> a
die msg = error $ "SBV->C: Unexpected: " ++ msg

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

data SBVToLLVM = SBVToLLVM

instance CgTarget SBVToLLVM where
  targetName _ = "LLVM"
  translate _  = cgen

floatT  = PrimType (FloatType Float)
doubleT = PrimType (FloatType Double)

data Intrinsics = Intrinsics { llvm_fabs_f32 :: Typed Value
                             , llvm_fabs_f64 :: Typed Value
                             }

-- | Declare intrinsics used by SBV.
declareIntrinsics :: LLVM Intrinsics
declareIntrinsics  =
  do llvm_fabs_f32 <- declare floatT  "llvm.fabs.f32" [ floatT] False
     llvm_fabs_f64 <- declare doubleT "llvm.fabs.f64" [doubleT] False
     return Intrinsics { .. }

cgen :: CgConfig -> String -> CgState -> Result -> CgPgmBundle
cgen cfg nm st sbvProg = result
  where

  -- TODO: revisit this use of cgInteger and cgReal
  result = CgPgmBundle (cgInteger cfg, cgReal cfg)
      [ ( nm ++ ".ll", (CgSource, [ppModule m]))
      ]

  (_,m) = runLLVM $
    do ints <- declareIntrinsics
       _ <- define' emptyFunAttrs rty (fromString nm) args False $ \ as ->
              do genLLVMProg ints sbvProg (zip as (cgInputs st))
                 end

       return ()

  (rty,end) =
    case cgReturns st of

      [] -> (voidT, retVoid)

      [CgAtomic o] ->
        let ty = llvmType (kindOf o)
         in (ty, ret (ty =: Ident (show o)))

      [CgArray _]  -> tbd "Non-atomic return values"

      _            -> tbd "Multiple return values"

  args = map mkParam (cgInputs st)

-- | Generate parameters for an LLVM function.
mkParam :: (String,CgVal) -> Type
mkParam (_, val) =
  case val of
    CgAtomic o       -> llvmType (kindOf o)
    CgArray os@(o:_) -> ptrT (arrayT (fromIntegral (length os))
                                     (llvmType (kindOf o)))
    CgArray _        -> die "mkParam: CgArray with no elements!"


-- | Translate from SBV Kinds to LLVM Types.
llvmType :: Kind -> Type
llvmType KBool          = PrimType (Integer 1)
llvmType (KBounded s w) = PrimType (Integer (fromIntegral w))
llvmType KFloat         = PrimType (FloatType Float)
llvmType KDouble        = PrimType (FloatType Double)
llvmType KUnbounded     = error "llvmType: KUnbounded"
llvmType KReal          = error "llvmType: KReal"
llvmType KUserSort{}    = error "llvmType: KUserSort"


genLLVMProg :: Intrinsics -> Result -> [(Typed Value, (String,CgVal))] -> BB ()
genLLVMProg ints
  (Result kindInfo _tvals cgs ins preConsts tbls arrs _ _ (SBVPgm asgns) cstrs _)
  args
  = do mapM_ rnArg args
       F.mapM_ (toStmt ints preConsts) asgns
  where

  rnArg (tv,(var,CgAtomic i)) =
    assign (fromString (show i)) (add tv (int 0))

  rnArg (_,(_,CgArray [])) =
    die "genLLVMProg: CgArray with no elements"

  -- rnArg (var,CgArray is) = concat (zipWith index [0 .. ] is)
  --     where
  --     index = GEP True 

cwValue :: CW -> Typed Value
cwValue (CW kind val) =
  case val of
    CWInteger i -> mk (toValue   i)
    CWFloat   f -> mk (ValFloat  f)
    CWDouble  d -> mk (ValDouble d)
    _           -> die "cwValue: unhandled value"

  where

  mk = Typed (llvmType kind)

swValue :: [(SW,CW)] -> SW -> Typed Value
swValue consts sw
  | sw == falseSW                 = mkTyped sw False
  | sw == trueSW                  = mkTyped sw True
  | Just cw <- sw `lookup` consts = mkConst cw
  | otherwise                     = mkTyped sw (Ident (show sw))

mkTyped :: (HasKind kind, IsValue a) => kind -> a -> Typed Value
mkTyped kind a = llvmType (kindOf kind) -: a

mkConst :: CW -> Typed Value
mkConst (CW KFloat           (CWFloat   f)) = llvmType KFloat  -: f
mkConst (CW KDouble          (CWDouble  f)) = llvmType KDouble -: f
mkConst (CW k@(KBounded s w) (CWInteger i)) = llvmType k       -: i

assignSW :: SW -> BB (Typed Value) -> BB (Typed Value)
assignSW sw = assign (Ident (show sw))

toStmt :: Intrinsics -> [(SW,CW)] -> (SW,SBVExpr) -> BB (Typed Value)
toStmt ints consts (res,SBVApp op sws) = assignSW res $ case op of

  Ite | [c,t,f] <- args ->
    select c t f

  UNeg | [a] <- args ->
      let zero = const (ValInteger 0) `fmap` a
          kind = kindOf (head sws)
       in llvmBinOp Minus kind (const (int 0) `fmap` a) a

  Abs | [a] <- args ->
    case kindOf (head sws) of
      KFloat           -> call (llvm_fabs_f32 ints) [a]
      KDouble          -> call (llvm_fabs_f64 ints) [a]
      KBounded False _ -> return a
      KBounded True  w -> do cond <- icmp Isgt a      (int 0)
                             a'   <- bxor a           (int (negate 1))
                             select cond a =<< add a' (int 1)
      kind             -> fail ("toStmt: unsupported kind for abs: " ++ show kind)

  -- Not is only ever used with i1
  Not | [a] <- args ->
    bxor a (1 :: Int)

      -- binary operators
  _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                , GreaterThan, And, Or ]
    , [a,b] <- args ->
      let kind = kindOf (head sws)
       in llvmBinOp op kind a b

  _ -> die $ "Received operator " ++ show op ++ " applied to " ++ show sws

  where

  args = map (swValue consts) sws

isFloating :: Kind -> Bool
isFloating KFloat  = True
isFloating KDouble = True
isFloating _       = False

isSigned :: Kind -> Bool
isSigned (KBounded s _) = s
isSigned k              = die ("isSigned: unexpected kind: " ++ show k)

llvmBinOp :: IsValue a => Op -> Kind -> Typed Value -> a -> BB (Typed Value)
llvmBinOp Plus  k | isFloating k = fadd
                  | otherwise    = add
llvmBinOp Minus k | isFloating k = fsub
                  | otherwise    = sub
llvmBinOp Times k | isFloating k = fmul
                  | otherwise    = mul

llvmBinOp Quot  k | isFloating k = fdiv
                  | isSigned   k = sdiv
                  | otherwise    = udiv

llvmBinOp Rem   k | isFloating k = frem
                  | isSigned   k = srem
                  | otherwise    = urem

llvmBinOp Equal k | isFloating k = fcmp Foeq
                  | otherwise    = icmp Ieq

llvmBinOp NotEqual k | isFloating k = fcmp Fone
                     | otherwise    = icmp Ine

llvmBinOp LessThan k | isFloating k = fcmp Folt
                     | otherwise    = icmp Iult

llvmBinOp GreaterThan k | isFloating k = fcmp Fogt
                        | otherwise    = icmp Iugt
