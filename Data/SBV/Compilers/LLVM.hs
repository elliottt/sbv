module Data.SBV.Compilers.LLVM where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex, showCFloat, showCDouble)
import Data.SBV.Compilers.CodeGen

import qualified Data.Foldable as F
import qualified Data.Sequence as Seq
import           System.Random (randoms,newStdGen)
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
      [ ( nm ++ ".ll", (CgSource, [LLVM.ppDefine def]))
      ]

  def = LLVM.Define { LLVM.defAttrs   = LLVM.emptyFunAttrs
                    , LLVM.defRetType = ret
                    , LLVM.defName    = LLVM.Symbol nm
                    , LLVM.defArgs    = args
                    , LLVM.defVarArgs = False
                    , LLVM.defSection = Nothing
                    , LLVM.defBody    = [body] }

  body = genLLVMProg sbvProg end

  (ret,end) =
    case cgReturns st of

      [] -> (LLVM.PrimType LLVM.Void, Nothing)

      [CgAtomic o] ->
        let ty = llvmType (kindOf o)
         in (ty, Just (LLVM.Typed ty (LLVM.ValIdent ((LLVM.Ident (show o))))))

      [CgArray _]  -> tbd "Non-atomic return values"

      _            -> tbd "Multiple return values"

  args = map mkParam (cgInputs st)

-- | Generate parameters for an LLVM function.
mkParam :: (String,CgVal) -> LLVM.Typed LLVM.Ident
mkParam (name, val) =
  LLVM.Typed { LLVM.typedValue = LLVM.Ident name
             , LLVM.typedType  = ty
             }
  where
  ty = case val of
         CgAtomic o       -> llvmType (kindOf o)
         CgArray os@(o:_) -> LLVM.Array (fromIntegral (length os))
                                        (llvmType (kindOf o))
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


genLLVMProg :: Result -> Maybe (LLVM.Typed LLVM.Value) -> LLVM.BasicBlock
genLLVMProg
  (Result kindInfo _tvals cgs ins preConsts tbls arrs _ _ (SBVPgm asgns) cstrs _)
  resVar
  = block
  where

  block =
    LLVM.BasicBlock { LLVM.bbLabel = Nothing
                    , LLVM.bbStmts = toStmts asgns ++ [retStmt] }

  retStmt =
    case resVar of
      Just var -> LLVM.Effect (LLVM.Ret var) []
      Nothing  -> LLVM.Effect LLVM.RetVoid   []

toStmts :: Seq.Seq (SW,SBVExpr) -> [LLVM.Stmt]
toStmts asgns = [ LLVM.Result (LLVM.Ident (show sw)) (toInstr e) []
                | (sw,e) <- F.toList asgns ]

swValue :: SW -> LLVM.Typed LLVM.Value
swValue sw =
  LLVM.Typed { LLVM.typedType  = llvmType (kindOf sw)
             , LLVM.typedValue = LLVM.ValIdent (LLVM.Ident (show sw)) }

toInstr :: SBVExpr -> LLVM.Instr
toInstr (SBVApp op sws) = case op of

  Ite | [c,t,f] <- args ->
    LLVM.Select c t (LLVM.typedValue f)

  UNeg | [a] <- args ->
      let zero = const (LLVM.ValInteger 0) `fmap` a
          kind = kindOf (head sws)
       in llvmBinOp Minus kind zero (LLVM.typedValue a)

      -- binary operators
  _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                , GreaterThan ]
    , [a,b] <- args ->
      let kind = kindOf (head sws)
       in llvmBinOp op kind a (LLVM.typedValue b)

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

llvmBinOp :: Op -> Kind -> LLVM.Typed LLVM.Value -> LLVM.Value -> LLVM.Instr
llvmBinOp Plus  k | isFloating k = LLVM.Arith  LLVM.FAdd
                  | otherwise    = LLVM.Arith (LLVM.Add False False)
llvmBinOp Minus k | isFloating k = LLVM.Arith  LLVM.FSub
                  | otherwise    = LLVM.Arith (LLVM.Sub False False)
llvmBinOp Times k | isFloating k = LLVM.Arith  LLVM.FMul
                  | otherwise    = LLVM.Arith (LLVM.Mul False False)

llvmBinOp Quot  k | isFloating k = LLVM.Arith  LLVM.FDiv
                  | isSigned   k = LLVM.Arith (LLVM.SDiv False)
                  | otherwise    = LLVM.Arith (LLVM.UDiv False)

llvmBinOp Rem   k | isFloating k = LLVM.Arith  LLVM.FRem
                  | isSigned   k = LLVM.Arith  LLVM.SRem
                  | otherwise    = LLVM.Arith  LLVM.URem

llvmBinOp Equal k | isFloating k = LLVM.FCmp LLVM.Foeq
                  | otherwise    = LLVM.ICmp LLVM.Ieq

llvmBinOp NotEqual k | isFloating k = LLVM.FCmp LLVM.Fone
                     | otherwise    = LLVM.ICmp LLVM.Ine

llvmBinOp LessThan k | isFloating k = LLVM.FCmp LLVM.Folt
                     | otherwise    = LLVM.ICmp LLVM.Iult

llvmBinOp GreaterThan k | isFloating k = LLVM.FCmp LLVM.Fogt
                        | otherwise    = LLVM.ICmp LLVM.Iugt
