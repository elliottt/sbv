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
                    , LLVM.defBody    = body }

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


genLLVMProg :: Result -> Maybe (LLVM.Typed LLVM.Value) -> [LLVM.BasicBlock]
genLLVMProg
  (Result kindInfo _tvals cgs ins preConsts tbls arrs _ _ (SBVPgm asgns) cstrs _)
  resVar
  = funBody (addEffect retStmt (toStmts asgns))
  where

  retStmt =
    case resVar of
      Just var -> LLVM.Ret var
      Nothing  -> LLVM.RetVoid


data PartialFun = PartialFun { pfBlock :: [LLVM.Stmt]
                               -- ^ The current block
                             , pfLabel :: LLVM.BlockLabel
                               -- ^ The current label
                             , pfBlocks :: [LLVM.BasicBlock]
                               -- ^ Finished blocks
                             , pfNext :: Int
                               -- ^ Fresh names
                             }

initialFun :: PartialFun
initialFun  = PartialFun { pfBlock  = []
                         , pfLabel  = LLVM.Named (LLVM.Ident "BB0")
                         , pfBlocks = []
                         , pfNext   = 1 }

addResult :: LLVM.Ident -> LLVM.Instr -> PartialFun -> PartialFun
addResult i instr pf = pf { pfBlock = LLVM.Result i instr [] : pfBlock pf }

newResult :: LLVM.Instr -> PartialFun -> (LLVM.Ident,PartialFun)
newResult instr pf =
  (name, addResult name instr pf { pfNext = pfNext pf + 1 })
  where
  name = LLVM.Ident ("res" ++ show (pfNext pf))

addEffect :: LLVM.Instr -> PartialFun -> PartialFun
addEffect instr pf = pf { pfBlock = LLVM.Effect instr [] : pfBlock pf }

-- | Close the current block, and return the name of the next block.
closeBlock :: PartialFun -> (LLVM.BlockLabel,PartialFun)
closeBlock pf = (label, pf { pfBlock  = []
                           , pfLabel  = label
                           , pfBlocks = block : pfBlocks pf
                           , pfNext   = pfNext pf + 1 })
  where
  label = LLVM.Named (LLVM.Ident ("BB" ++ show (pfNext pf)))

  block =
    LLVM.BasicBlock { LLVM.bbLabel = Just (pfLabel pf)
                    , LLVM.bbStmts = reverse (pfBlock pf) }

funBody :: PartialFun -> [LLVM.BasicBlock]
funBody pf = reverse (pfBlocks (snd (closeBlock pf)))

toStmts :: Seq.Seq (SW,SBVExpr) -> PartialFun
toStmts  = F.foldl (flip toStmt) initialFun

swValue :: SW -> LLVM.Typed LLVM.Value
swValue sw =
  LLVM.Typed { LLVM.typedType  = llvmType (kindOf sw)
             , LLVM.typedValue = LLVM.ValIdent (LLVM.Ident (show sw)) }

toStmt :: (SW,SBVExpr) -> PartialFun -> PartialFun
toStmt (res,SBVApp op sws) pf = case op of

  Ite | [c,t,f] <- args ->
    let (lt,pft0) = closeBlock (addEffect (LLVM.Br c lt lf) pf)

        (rt,pft1) = newResult (LLVM.Alloca resTy Nothing Nothing) pft0
        (lf,pff0) = closeBlock
                  $ addEffect (LLVM.Jump lk)
                  $ addEffect (LLVM.Store t (resPtr rt) Nothing) pft1

        (rf,pff1) = newResult (LLVM.Alloca resTy Nothing Nothing) pff0
        (lk,pf')  = closeBlock
                  $ addEffect (LLVM.Jump lk)
                  $ addEffect (LLVM.Store f (resPtr rf) Nothing) pff1

     in addResult resVal (LLVM.Phi resTy [ (LLVM.ValIdent rt, lt)
                                         , (LLVM.ValIdent rf, lf) ]) pf'

  UNeg | [a] <- args ->
      let zero = const (LLVM.ValInteger 0) `fmap` a
          kind = kindOf (head sws)
       in addResult resVal (llvmBinOp Minus kind zero (LLVM.typedValue a)) pf

      -- binary operators
  _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                , GreaterThan ]
    , [a,b] <- args ->
      let kind = kindOf (head sws)
       in addResult resVal (llvmBinOp op kind a (LLVM.typedValue b)) pf

  _ -> die $ "Received operator " ++ show op ++ " applied to " ++ show sws

  where

  resTy    = llvmType (kindOf res)
  resPtr p = LLVM.Typed (LLVM.PtrTo resTy) (LLVM.ValIdent p)
  resVal   = LLVM.Ident (show res)

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
