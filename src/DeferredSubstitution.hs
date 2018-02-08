{-# language DeriveFunctor #-}

-- | An implementation of the formal system in Ben Lippmeier's "Don't
-- Substitute Into Abstractions (Functional Pearl)"
module DeferredSubstitution where

import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text)

import qualified Data.Map.Strict as Map

newtype Name = Name Text
  deriving (Eq, Ord)

data Type
  = TyUnit
  | TyArr Type Type

data Term
  = Var Name
  | Abs Sub Name Type Term
  | App Term Term

newtype VarMap a = VarMap (Map Name a)
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
type Sub = VarMap Term

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

type Env = VarMap Type

-- @lookup_E@ in the paper
lookupEnv :: Name -> Env -> Maybe Type
lookupEnv = lookup'
