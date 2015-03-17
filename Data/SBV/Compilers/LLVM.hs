module Data.SBV.Compilers.LLVM where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex, showCFloat, showCDouble)
import Data.SBV.Compilers.CodeGen

import qualified Data.Foldable as F
import qualified Data.Sequence as Seq
import           Data.String (IsString(..))
import           System.Random (randoms,newStdGen)
import           Text.LLVM hiding (Result)
import qualified Text.LLVM.AST as LLVM
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

cgen :: CgConfig -> String -> CgState -> Result -> CgPgmBundle
cgen cfg nm st sbvProg = result
  where

  -- TODO: revisit this use of cgInteger and cgReal
  result = CgPgmBundle (cgInteger cfg, cgReal cfg)
      [ ( nm ++ ".ll", (CgSource, [LLVM.ppModule m]))
      ]

  (_,m) = runLLVM $
    do _ <- define' emptyFunAttrs rty (fromString nm) args False $ \ as ->
              do genLLVMProg sbvProg (zip as (cgInputs st))
                 end

       return ()

  (rty,end) =
    case cgReturns st of

      [] -> (voidT, retVoid)

      [CgAtomic o] ->
        let ty = llvmType (kindOf o)
         in (ty, ret (ty =: LLVM.Ident (show o)))

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
llvmType :: Kind -> LLVM.Type
llvmType KBool          = LLVM.PrimType (LLVM.Integer 1)
llvmType (KBounded s w) = LLVM.PrimType (LLVM.Integer (fromIntegral w))
llvmType KFloat         = LLVM.PrimType (LLVM.FloatType LLVM.Float)
llvmType KDouble        = LLVM.PrimType (LLVM.FloatType LLVM.Double)
llvmType KUnbounded     = error "llvmType: KUnbounded"
llvmType KReal          = error "llvmType: KReal"
llvmType KUserSort{}    = error "llvmType: KUserSort"


genLLVMProg :: Result -> [(Typed Value, (String,CgVal))] -> BB ()
genLLVMProg
  (Result kindInfo _tvals cgs ins preConsts tbls arrs _ _ (SBVPgm asgns) cstrs _)
  args
  = do mapM_ rnArg args
       mapM_ mkConst preConsts
       F.mapM_ toStmt asgns
  where

  rnArg (tv,(var,CgAtomic i)) =
    assign (fromString (show i)) (add tv (0 :: Integer))

  rnArg (_,(_,CgArray [])) =
    die "genLLVMProg: CgArray with no elements"

  -- rnArg (var,CgArray is) = concat (zipWith index [0 .. ] is)
  --     where
  --     index = LLVM.GEP True 

cwValue :: CW -> LLVM.Typed LLVM.Value
cwValue (CW kind val) =
  case val of
    CWInteger i -> mk (toValue   i)
    CWFloat   f -> mk (ValFloat  f)
    CWDouble  d -> mk (ValDouble d)
    _           -> die "cwValue: unhandled value"

  where

  mk = LLVM.Typed (llvmType kind)

swValue :: SW -> Typed Value
swValue sw = llvmType (kindOf sw) -: Ident (show sw)

mkConst :: (SW,CW) -> BB (Typed Value)
mkConst (res,cw) =
  assign (fromString (show res))
         (llvmBinOp Plus (kindOf cw) cwVal zero)
  where
  cwVal = cwValue cw
  zero  = const (toValue (0 :: Integer)) `fmap` cwVal


toStmt :: (SW,SBVExpr) -> BB (Typed Value)
toStmt (res,SBVApp op sws) = case op of

  Ite | [c,t,f] <- args ->
    assign (fromString (show res)) (select c t f)

  UNeg | [a] <- args ->
      let zero = const (LLVM.ValInteger 0) `fmap` a
          kind = kindOf (head sws)
       in assign (fromString (show res)) (llvmBinOp Minus kind zero a)

      -- binary operators
  _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                , GreaterThan ]
    , [a,b] <- args ->
      let kind = kindOf (head sws)
       in assign (fromString (show res)) (llvmBinOp op kind a b)

  _ -> die $ "Received operator " ++ show op ++ " applied to " ++ show sws

  where

  args = map swValue sws

isFloating :: Kind -> Bool
isFloating KFloat  = True
isFloating KDouble = True
isFloating _       = False

isSigned :: Kind -> Bool
isSigned (KBounded s _) = s
isSigned k              = die ("isSigned: unexpected kind: " ++ show k)

llvmBinOp :: Op -> Kind -> Typed Value -> Typed Value -> BB (Typed Value)
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
