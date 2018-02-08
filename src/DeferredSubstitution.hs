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

-- | A "right-biased simultaneous priority substitution"
--
-- We use a @Map@ here because we don't require the simplified semantics of the
-- paper -- we never pop our "stack", so we can overwrite earlier names in the
-- substitution.
--
-- We're right-biased in that @Map@ 'insert' overwrites, and our 'mappend' is
-- right-biased.
newtype Sub = Sub { _subMap :: Map Name Term }

instance Monoid Sub where
  mempty = Sub mempty
  mappend (Sub mapL) (Sub mapR) = Sub $ Map.union mapR mapL -- NOTE: right bias

lookupSub :: Name -> Sub -> Maybe Term
lookupSub name (Sub terms) = Map.lookup name terms

-- @subst@ in the paper
-- | The application of an explicit substitution, theta, to a term.
substitute :: Sub -> Term -> Term
substitute theta var@(Var name) = fromMaybe var $ lookupSub name theta
substitute outer (Abs inner var ty body) = Abs theta var ty body
  where
    theta = outer <> Sub (substitute outer <$> _subMap inner)
substitute theta (App t0 t1) = App (substitute theta t0) (substitute theta t1)

-- @lookup_E@ in the paper
--lookupEnv :: Name -> Env -> Maybe Type
