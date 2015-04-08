{-# LANGUAGE RecordWildCards #-}

module Data.SBV.Compilers.LLVM (
  compileToLLVM,
  compileToLLVM'
  ) where

import Data.SBV.BitVectors.Data
import Data.SBV.Compilers.CodeGen

import           Control.Monad (foldM,zipWithM_)
import qualified Data.Foldable as F
import           Data.List (partition)
import qualified Data.Map.Strict as Map
import           Data.Maybe (isJust)
import qualified Data.Sequence as Seq
import           Data.String (IsString(..))
import           System.Random (randoms,newStdGen)
import           Text.LLVM hiding (Result,And,Or,Xor,Shl)


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
die msg = error $ "SBV->LLVM: Unexpected: " ++ msg

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->LLVM: Not yet supported: " ++ msg

data SBVToLLVM = SBVToLLVM

instance CgTarget SBVToLLVM where
  targetName _ = "LLVM"
  translate _  = cgen

floatT, doubleT :: Type
floatT  = PrimType (FloatType Float)
doubleT = PrimType (FloatType Double)

data Intrinsics = Intrinsics { llvm_fabs_f32 :: Typed Value
                             , llvm_fabs_f64 :: Typed Value
                             }

-- | Declare intrinsics used by SBV.
declareIntrinsics :: LLVM Intrinsics
declareIntrinsics  =
  do llvm_fabs_f32 <- declare floatT  (Symbol "llvm.fabs.f32") [ floatT] False
     llvm_fabs_f64 <- declare doubleT (Symbol "llvm.fabs.f64") [doubleT] False
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
       env  <- bindTables (map snd globalTables)
                   =<< bindUninterpreted us (bindConsts consts emptyEnv)
       _ <- define' emptyFunAttrs rty (fromString nm) (ins ++ outs) False $ \ as ->
              do let (is,os) = splitAt (length ins) as
                 env' <- genLLVMProg cfg env ints (zip is (cgInputs  st))
                                                  (zip os (cgOutputs st))
                                                  stmts
                 end env'

       return ()

  Result _ _ _ _ consts tbls _ us _ (SBVPgm asgns) _ _ = sbvProg

  -- partition the tables out into constant and data-dependent definitions
  (globalTables,depTables) = partition (\ (i,_) -> i == -1)
                                [ (tableId vals, t) | t@(_,vals) <- tbls ]
  tableId vals = maximum (-1 : map getNodeId vals)


  -- merge table declarations and assignments
  stmts = fmap snd
        $ Seq.sortBy compareStmt
        $ Seq.fromList [ (n,MakeTable t) | (n,t) <- depTables ]
   Seq.>< fmap addNodeId asgns
    where
    compareStmt (i,l) (j,r)
      | i < j     = LT
      | otherwise = GT

  addNodeId a@(sw,_) = (getNodeId sw, MakeAssign a)

  -- retrieve the id of a variable, or produce -1 in the case of a constant
  getNodeId s@(SW _ (NodeId n)) | constSw s = -1
                                | True      = n
  constSw s = isJust (lookup s consts)

  -- determine the return type of the function, and produce an action in the BB
  -- monad that will handle returning results (if there are any)
  (rty,end) =
    case cgReturns st of

      [] -> (voidT, const retVoid)

      [CgAtomic o] -> (llvmType (kindOf o), \env -> ret (swValue env o))

      [CgArray _]  -> tbd "Non-atomic return values"

      _            -> tbd "Multiple return values"

  -- the list of types for both inputs and outputs, used to produce the
  -- prototype
  ins  = map mkInput  (cgInputs  st)
  outs = map mkOutput (cgOutputs st)

-- | Generate parameters for an LLVM function.
mkInput :: (String,CgVal) -> Type
mkInput (_, val) =
  case val of
    CgAtomic o       -> llvmType (kindOf o)
    CgArray os@(o:_) -> ptrT (arrayT (fromIntegral (length os))
                                     (llvmType (kindOf o)))
    CgArray _        -> die "mkInput: CgArray with no elements!"

-- | Generate output parameters for an LLVM function.
mkOutput :: (String,CgVal) -> Type
mkOutput (_,val) =
  case val of
    CgAtomic o       -> ptrT (llvmType (kindOf o))
    CgArray os@(o:_) -> ptrT (arrayT (fromIntegral (length os))
                                     (llvmType (kindOf o)))
    CgArray _        -> die "mkOutput: CgArray with no elements!"


-- | Translate from SBV Kinds to LLVM Types.
llvmType :: Kind -> Type
llvmType KBool          = PrimType (Integer 1)
llvmType (KBounded _ w) = PrimType (Integer (fromIntegral w))
llvmType KFloat         = PrimType (FloatType Float)
llvmType KDouble        = PrimType (FloatType Double)
llvmType KUnbounded     = error "llvmType: KUnbounded"
llvmType KReal          = error "llvmType: KReal"
llvmType KUserSort{}    = error "llvmType: KUserSort"


genLLVMProg :: CgConfig
            -> Env -> Intrinsics
            -> [(Typed Value, (String,CgVal))]
            -> [(Typed Value, (String,CgVal))]
            -> Seq.Seq SbvStmt
            -> BB Env
genLLVMProg cfg env1 ints
  args outs stmts
  = do env2 <- foldM rnArg env1 args
       env3 <- F.foldlM (toStmt cfg ints) env2 stmts
       mapM_ (storeOutput env3) outs
       return env3
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


storeOutput :: Env -> (Typed Value, (String,CgVal)) -> BB ()

storeOutput env (tv, (_, CgAtomic o)) =
  store (swValue env o) tv Nothing

storeOutput env (tv, (_, CgArray os@(e:_))) =
  zipWithM_ storeAt [0 ..] os
  where
  ty = PtrTo (llvmType (kindOf e))

  storeAt :: Int -> SW -> BB ()
  storeAt off o =
    do ptr <- getelementptr ty tv [ iT 32 -: (0 :: Int), iT 32 -: off ]
       store (swValue env o) ptr Nothing

storeOutput _ (_, (_, CgArray [])) =
  die "storeOutput: empty output array"


-- Environment -----------------------------------------------------------------

-- | The mapping from names in SBV to names in the generated assembly.
data Env = Env { envValues        :: Map.Map SW (Typed Value)
               , envTables        :: Map.Map Int (Typed Value)
               , envUninterpreted :: Map.Map String (Typed Value)
               } deriving (Show)

emptyEnv :: Env
emptyEnv  = Env { envValues = Map.empty
                , envTables = Map.empty
                , envUninterpreted = Map.empty }

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

    _   -> do let (args,[rty]) = splitAt (length ts - 1) ts
              tv <- declare (llvmType rty) (Symbol n) (map llvmType args) False
              return (Map.insert n tv env)

-- | Add a table to the environment.
bindTable :: Int -> Typed Value -> Env -> Env
bindTable i t Env { .. } = Env { envTables = Map.insert i t envTables, .. }

-- | Emit tables as top-level constants.
--
-- NOTE: this should only be used when the elements are all constants.
bindTables :: [((Int, Kind, Kind), [SW])] -> Env -> LLVM Env
bindTables ts env0 @ Env { .. } =
  do new <- foldM addTable envTables ts
     return Env { envTables = new, .. }
  where

  addTable env ((ix, _, k), elts) =
    do let attrs = GlobalAttrs { gaLinkage  = Just Internal
                               , gaConstant = True }
           vals  = array (llvmType k) [ typedValue (swValue env0 sw) | sw <- elts ]

       table <- global attrs (Symbol ("table" ++ show ix))
                     (typedType vals)
                     (Just (typedValue vals))

       return (Map.insert ix table env)

bindValue :: SW -> Typed Value -> Env -> Env
bindValue sw tv Env { .. } = Env { envValues = Map.insert sw tv envValues, .. }

lookupSW :: SW -> Env -> Maybe (Typed Value)
lookupSW sw Env { .. } = Map.lookup sw envValues

-- | Lookup a table in the environment.
lookupTable :: Int -> Env -> Maybe (Typed Value)
lookupTable ix env = Map.lookup ix (envTables env)

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


-- Statements ------------------------------------------------------------------

data SbvStmt = MakeTable  ((Int,Kind,Kind),[SW])
             | MakeAssign (SW,SBVExpr)
               deriving (Show)

toStmt :: CgConfig -> Intrinsics -> Env -> SbvStmt -> BB Env
toStmt CgConfig { .. } ints env sbv = stmts sbv

  where

  nameResult sw val = return (bindValue sw val env)

  stmts (MakeTable ((ix,_,k),vals)) =
    do let eTy = llvmType k
       table <- alloca (arrayT (fromIntegral (length vals)) eTy)
                    Nothing Nothing

       let loadEntry off val =
             do ptr <- getelementptr (ptrT eTy) table [ iT 32 =: int 0
                                                      , iT 32 =: int off ]
                store (swValue env val) ptr Nothing

       zipWithM_ loadEntry [0 ..] vals

       return (bindTable ix table env)

  stmts (MakeAssign (res,SBVApp op sws)) = nameResult res =<< case op of

    Ite | [c,t,f] <- args ->
      select c t f

    UNeg | [a] <- args ->
        let kind = kindOf (head sws)
         in llvmBinOp Minus kind (const (int 0) `fmap` a) a

    Abs | [a] <- args ->
      case kindOf (head sws) of
        KFloat           -> call (llvm_fabs_f32 ints) [a]
        KDouble          -> call (llvm_fabs_f64 ints) [a]
        KBounded False _ -> return a
        KBounded True  _ -> do cond <- icmp Isgt a      (int 0)
                               a'   <- bxor a           (int (negate 1))
                               select cond a =<< add a' (int 1)
        kind             -> die ("toStmt: unsupported kind for abs: " ++ show kind)

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
        _            -> die "Invalid arguments to Ror"

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


    -- table lookup
    LkUp (tblIx, _, resTy, len) ix def ->
      case lookupTable tblIx env of
        Just table -> tableLookup cgRTC env resTy table len (swValue env ix)
                                                            (swValue env def)
        Nothing    -> die ("LkUp: Unknown table index: " ++ show tblIx)

      where

        -- binary operators
    _ | op `elem` [ Plus, Times, Minus, Quot, Rem, Equal, NotEqual, LessThan
                  , GreaterThan, And, Or, XOr ]
      , [a,b] <- args ->
        let kind = kindOf (head sws)
         in llvmBinOp op kind a b

    FPRound _ -> tbd "FPRound"

    _ -> die $ "Received operator " ++ show op ++ " applied to " ++ show sws

    where

    args = map (swValue env) sws


tableLookup :: Bool -> Env
            -> Kind -> Typed Value -> Int -> Typed Value -> Typed Value
            -> BB (Typed Value)
tableLookup rtc env resK table len ix def
    -- explicitly disabled index checks
  | not rtc   = lookupEntry
  | otherwise = undefined

  where
  resTy = ptrT (llvmType resK)

  lookupEntry =
    do ptr <- getelementptr resTy table [ iT 32 -: (0 :: Int), ix ]
       load ptr Nothing

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

llvmBinOp op _ = \ _ _ -> die ("llvmBinOp: Unsupported operation: " ++ show op)
