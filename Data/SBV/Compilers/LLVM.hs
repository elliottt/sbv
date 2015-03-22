{-# LANGUAGE RecordWildCards #-}

module Data.SBV.Compilers.LLVM (
  compileToLLVM,
  compileToLLVM'
  ) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex, showCFloat, showCDouble)
import Data.SBV.Compilers.CodeGen

import           Control.Monad (foldM)
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import           Data.String (IsString(..))
import           System.Random (randoms,newStdGen)
import           Text.LLVM hiding (Result,And,Or,Xor,Shl,Shr)
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
       env  <- bindUninterpreted us emptyEnv
       _ <- define' emptyFunAttrs rty (fromString nm) args False $ \ as ->
              do env <- genLLVMProg env ints sbvProg (zip as (cgInputs st))
                 end env

       return ()

  Result _ _ _ _ _ _ _ us _ _ _ _ = sbvProg

  (rty,end) =
    case cgReturns st of

      [] -> (voidT, const retVoid)

      [CgAtomic o] -> (llvmType (kindOf o), \env -> ret (swValue env o))

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


genLLVMProg :: Env -> Intrinsics -> Result -> [(Typed Value, (String,CgVal))]
            -> BB Env
genLLVMProg env0 ints
  (Result kindInfo _ cgs ins preConsts tbls arrs us _ (SBVPgm asgns) cstrs _)
  args
  = do let env1 = bindConsts preConsts env0
       env2 <- foldM rnArg env1 args
       F.foldlM (toStmt ints) env2 asgns
  where

  -- add entries in the environment for mappings to arguments
  rnArg cs (tv,(_,CgAtomic i)) =
    return (bindValue i tv cs)

  rnArg _ (_,(_,CgArray [])) =
    die "genLLVMProg: CgArray with no elements"

  rnArg cs (arg,(_,CgArray is)) =
    do arr <- load arg Nothing
       foldM (unpackArg arr) cs (zip [0 .. ] is)

  unpackArg arr cs (off,i) =
    do tv <- extractValue arr off
       return (bindValue i tv cs)


-- Environment -----------------------------------------------------------------

-- | The mapping from names in SBV to names in the generated assembly.
data Env = Env { envValues        :: Map.Map SW (Typed Value)
               , envUninterpreted :: Map.Map String (Typed Value)
               }

emptyEnv :: Env
emptyEnv  = Env { envValues = Map.empty, envUninterpreted = Map.empty }

bindConsts :: [(SW,CW)] -> Env -> Env
bindConsts cs Env { .. } = Env { envValues = Map.union new envValues, .. }
  where
  new = Map.fromList [ (sw, cwValue cw) | (sw,cw) <- cs ]

-- | Bind uninterpreted constants, and declare them in the resulting module.
bindUninterpreted :: [(String,SBVType)] -> Env -> LLVM Env
bindUninterpreted us Env { .. } =
  do new <- foldM addDec envUninterpreted us
     return Env { envUninterpreted = new, .. }
  where

  addDec env (n, SBVType ts) = case ts of

    []  -> die "bindUninterpreted: Invalid SBVType"

    [t] -> do let attrs = GlobalAttrs { gaLinkage  = Just External
                                      , gaConstant = True }
              tv <- global attrs (Symbol n) (llvmType t) Nothing
              return (Map.insert n tv env)

    _   -> do let (args,[ret]) = splitAt (length ts - 1) ts
              tv <- declare (llvmType ret) (Symbol n) (map llvmType args) False
              return (Map.insert n tv env)


bindValue :: SW -> Typed Value -> Env -> Env
bindValue sw tv Env { .. } = Env { envValues = Map.insert sw tv envValues, .. }

lookupSW :: SW -> Env -> Maybe (Typed Value)
lookupSW sw Env { .. } = Map.lookup sw envValues

lookupUninterpreted :: String -> Env -> Maybe (Typed Value)
lookupUninterpreted n Env { .. } = Map.lookup n envUninterpreted


-- Values ----------------------------------------------------------------------

cwValue :: CW -> Typed Value
cwValue (CW kind val) =
  case val of
    CWInteger i -> mk (toValue   i)
    CWFloat   f -> mk (ValFloat  f)
    CWDouble  d -> mk (ValDouble d)
    _           -> die "cwValue: unhandled value"

  where

  mk = Typed (llvmType kind)

swValue :: Env -> SW -> Typed Value
swValue env sw
  | sw == falseSW                = mkTyped sw False
  | sw == trueSW                 = mkTyped sw True
  | Just tv <- sw `lookupSW` env = tv
  | otherwise                    = mkTyped sw (Ident (show sw))

mkTyped :: (HasKind kind, IsValue a) => kind -> a -> Typed Value
mkTyped kind a = llvmType (kindOf kind) -: a

mkConst :: CW -> Typed Value
mkConst (CW KFloat           (CWFloat   f)) = llvmType KFloat  -: f
mkConst (CW KDouble          (CWDouble  f)) = llvmType KDouble -: f
mkConst (CW k@(KBounded s w) (CWInteger i)) = llvmType k       -: i


-- Statements ------------------------------------------------------------------

toStmt :: Intrinsics -> Env -> (SW,SBVExpr) -> BB Env
toStmt ints env (res,SBVApp op sws) =
  do val <- stmts
     return (bindValue res val env)

  where
  stmts = case op of

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

    -- shift left
    Shl n | [a] <- args ->
      shl a n

    -- shift right
    Shr n | [a] <- args ->
      case kindOf (head sws) of
        KBounded True  _ -> ashr a (n :: Int)
        KBounded False _ -> lshr a (n :: Int)
        k                -> die $ "Unsupported kind to Shr: " ++ show k

    -- rotate left
    Rol n | [a] <- args ->
      case kindOf (head sws) of
        KBounded _ w -> do u <- shl a n
                           l <- lshr a (w - n)
                           bor u l
        _            -> die "Invalid arguments to Rol"

    Ror n | [a] <- args ->
      case kindOf (head sws) of
        KBounded _ w -> do u <- shl  a (w - n)
                           l <- lshr a n
                           bor u l

    -- sizeof a > i >= j >= 0
    Extract i j | [a] <- args ->

      case (kindOf (head sws), kindOf res) of

        (KBounded False m, KBounded False n)
          | n == i - j + 1 ->
            do val <- if j > 0 then lshr a j
                               else return a

               if m > n
                  then trunc val (iT (fromIntegral n))
                  else return val

        _ -> die ("Malformed Extract: " ++ show op ++ " " ++ show sws)


    -- join is only ever called with unsigned arguments
    Join | [a,b] <- args ->
      case map kindOf sws of
        [ KBounded False la, KBounded False lb ] ->
          do let ty = iT (fromIntegral (la + lb))
             a'  <- zext a ty
             b'  <- zext b ty
             a'' <- shl a' lb
             bor a'' b'

        _ -> die $ "Join applied to " ++ show sws

    ArrEq   _ _ -> tbd "User specified arrays (ArrEq)"
    ArrRead _   -> tbd "User specified arrays (ArrRead)"

    Uninterpreted s
      | Just tv <- lookupUninterpreted s env ->
        if null args
           then load tv Nothing
           else call tv args

      | otherwise ->
        die ("Unknown uninterpreted constant: " ++ s)

        -- binary operators
    _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                  , GreaterThan, And, Or, XOr ]
      , [a,b] <- args ->
        let kind = kindOf (head sws)
         in llvmBinOp op kind a b

    FPRound str -> tbd "FPRound"

    _ -> die $ "Received operator " ++ show op ++ " applied to " ++ show sws

  args = map (swValue env) sws

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

llvmBinOp And _ = band
llvmBinOp Or  _ = bor
llvmBinOp XOr _ = bxor
