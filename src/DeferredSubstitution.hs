{-# language GeneralizedNewtypeDeriving #-}

-- | An implementation of the formal system in Ben Lippmeier's "Don't
-- Substitute Into Abstractions (Functional Pearl)"
module DeferredSubstitution where

import Control.Monad (when)
import Control.Monad.Except (ExceptT(..), MonadError(..))
import Control.Monad.Reader (Reader, MonadReader(ask, local))
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.String (IsString(..))
import Data.Text (Text)

import qualified Data.Map.Strict as Map
import qualified Data.Text as T

newtype Name
  = Name Text
  deriving (Eq, Ord)

data Type
  = TyUnit
  | TyArr Type Type
  deriving (Eq)

data Term
  = Unit
  | Var Name
  | Abs Sub Name Type Term
  | App Term Term

newtype VarMap a
  = VarMap (Map Name a)
  deriving Functor

instance Monoid (VarMap a) where
  mempty = VarMap mempty
  mappend (VarMap l) (VarMap r) = VarMap $ Map.union r l -- NOTE: right bias

mappedTo :: Name -> a -> VarMap a
name `mappedTo` a = VarMap $ Map.singleton name a

-- | A "right-biased simultaneous priority substitution"
--
-- We use a @Map@ here because we don't require the simplified semantics of the
-- paper -- we never pop our "stack", so we can overwrite earlier names in the
-- substitution.
--
-- We're right-biased in that @VarMap@'s @Map@ 'insert' overwrites, and our
-- 'mappend' is right-biased.
type Sub
  = VarMap Term

lookup' :: Name -> VarMap a -> Maybe a
lookup' name (VarMap m) = Map.lookup name m

-- @lookup_S@ in the paper
lookupSub :: Name -> Sub -> Maybe Term
lookupSub = lookup'

-- @subst@ in the paper
-- | The application of an explicit substitution, theta, to a term.
substitute :: Sub -> Term -> Term
substitute _theta Unit = Unit
substitute theta var@(Var name) = fromMaybe var $ lookupSub name theta
substitute outer (Abs inner var ty body) = Abs theta var ty body
  where
    theta = outer <> (substitute outer <$> inner)
substitute theta (App t0 t1) = App (substitute theta t0) (substitute theta t1)

type Env
  = VarMap Type

-- @lookup_E@ in the paper
lookupEnv :: Name -> Env -> Maybe Type
lookupEnv = lookup'

data TypeError
  = NotInScope Name
  | TypeMismatch { _mismatchExpected :: Type
                 , _mismatchActual   :: Type }
  | ExpectedFunctionType { _efNonFunction     :: Term
                         , _efNonFunctionType :: Type
                         , _efArg             :: Term
                         , _efArgType         :: Type }

newtype CheckM a
  = CheckM { runCheckM :: ExceptT TypeError (Reader Env) a }
  deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader Env)

typeInEnv :: Name -> CheckM (Maybe Type)
typeInEnv name = lookupEnv name <$> ask

-- extend/shadow the typing context with a new binding
assuming :: Name -> Type -> CheckM a -> CheckM a
assuming name ty = local (<> name `mappedTo` ty)

shouldBe :: Type -> Type -> CheckM ()
actual `shouldBe` expected = when (expected /= actual) $
  throwError $ TypeMismatch expected actual

check :: Type -> Term -> CheckM ()
check ty Unit = ty `shouldBe` TyUnit
check ty (Var name) = do
  mTy' <- typeInEnv name
  case mTy' of
    Just ty' -> ty' `shouldBe` ty
    Nothing -> throwError $ NotInScope name
check (TyArr inTy outTy) (Abs _theta name paramTy body) = do
  paramTy `shouldBe` inTy
  assuming name paramTy $ check outTy body
check ty term@(Abs _ _ _ _) = do
  ty' <- infer term -- infer a type for our error message
  ty' `shouldBe` ty -- always errors, because ty' is not TyArr
check ty (t0 `App` t1) = do
  argTy <- infer t1
  check (TyArr argTy ty) t0

infer :: Term -> CheckM Type
infer Unit = return TyUnit
infer (Var name) = do
  mTy <- typeInEnv name
  case mTy of
    Just ty -> return ty
    Nothing -> throwError $ NotInScope name
infer (Abs _theta _name argTy body) = TyArr argTy <$> infer body
infer (App t0 t1) = do
  argTy <- infer t1
  funTy <- infer t0
  case funTy of
    TyArr inTy outTy -> do
      argTy `shouldBe` inTy -- inTy is primary here: it's annotated on the abs
      return outTy
    _ -> throwError $ ExpectedFunctionType t0 funTy t1 argTy

isValue :: Term -> Bool
isValue Unit = True
isValue (Var _) = False
isValue (Abs _ _ _ _) = True -- ValueAbs
isValue (App _ _) = False

-- whether a term is in weak head normal form
isDone :: Term -> Bool
isDone (Var _) = True                             -- DoneVar
isDone (App t0 _) = isDone t0 && not (isValue t0) -- DoneApp
isDone term = isValue term                        -- DoneValue

data EvalError
  = UnboundVariable Name
  | ExpectedFunction Term Term

eval :: Term -> Either EvalError Term
eval Unit = return $ Unit
eval (Var name) = throwError $ UnboundVariable name
eval term@(Abs _ _ _ _) = return term
eval (App t0 t1) =
  if isValue t0
  then if isDone t1
       then case t0 of
              Abs theta name _argTy body ->       -- EsReduce
                eval $ substitute (theta <> (name `mappedTo` t1)) body
              _ -> throwError $ ExpectedFunction t0 t1
       else eval t1 >>= \t1' -> eval (App t0 t1') -- EsAppRight
  else eval t0 >>= \t0' -> eval (App t0' t1)      -- EsAppLeft
