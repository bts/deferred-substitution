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
import Data.Text (Text)

import qualified Data.Map.Strict as Map

newtype Name
  = Name Text
  deriving (Eq, Ord)

data Type
  = TyUnit
  | TyArr Type Type
  deriving (Eq)

data Term
  = Var Name
  | Abs Sub Name Type Term
  | App Term Term

newtype VarMap a
  = VarMap (Map Name a)
  deriving Functor

instance Monoid (VarMap a) where
  mempty = VarMap mempty
  mappend (VarMap l) (VarMap r) = VarMap $ Map.union r l -- NOTE: right bias

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
  = UnboundVariable Name
  | TypeMismatch { _mismatchExpected :: Type
                 , _mismatchActual   :: Type }
  | UnexpectedFunction { _ufFunction :: Term
                       , _ufType     :: Type }
  | ExpectedFunction { _efNonFunction :: Term
                     , _efArgument    :: Term
                     , _efArgType     :: Type }

newtype CheckM a
  = CheckM { runCheckM :: ExceptT TypeError (Reader Env) a }
  deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader Env)

typeInEnv :: Name -> CheckM (Maybe Type)
typeInEnv name = lookupEnv name <$> ask

-- extend/shadow the typing context with a new binding
assuming :: Name -> Type -> CheckM a -> CheckM a
assuming name ty = local (<> singletonEnv)
  where
    singletonEnv :: Env
    singletonEnv = VarMap $ Map.singleton name ty

shouldBe :: Type -> Type -> CheckM ()
actual `shouldBe` expected = when (expected /= actual) $
  throwError $ TypeMismatch expected actual

check :: Type -> Term -> CheckM ()
check ty (Var name) = do
  mTy' <- typeInEnv name
  case mTy' of
    Just ty' -> ty' `shouldBe` ty
    Nothing -> throwError $ UnboundVariable name
check (TyArr inTy outTy) (Abs _theta name paramTy body) = do
  paramTy `shouldBe` inTy
  assuming name paramTy $ check outTy body
check ty term@(Abs _ _ _ _) = throwError $ UnexpectedFunction term ty
check ty (t0 `App` t1) = do
  argTy <- infer t1
  check (TyArr argTy ty) t0

infer :: Term -> CheckM Type
infer (Var name) = do
  mTy <- typeInEnv name
  case mTy of
    Just ty -> return ty
    Nothing -> throwError $ UnboundVariable name
infer (Abs _theta _name argTy body) = TyArr argTy <$> infer body
infer (App t0 t1) = do
  argTy <- infer t1
  funTy <- infer t0
  case funTy of
    TyArr inTy outTy -> do
      argTy `shouldBe` inTy -- inTy is primary here: it's annotated on the abs
      return outTy
    _ -> throwError $ ExpectedFunction t0 t1 argTy
