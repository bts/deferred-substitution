-- | An implementation of the formal system in Ben Lippmeier's "Don't
-- Substitute Into Abstractions (Functional Pearl)"
module DeferredSubstitution where

import Data.Sequence ((><), Seq(..))
import Data.Text (Text)

newtype Name = Name Text
  deriving Eq

data Type
  = TyUnit
  | TyArr Type Type

data Term
  = Var Name
  | Abs Sub Name Type Term
  | App Term Term

-- | A "right-biased simultaneous priority substitution"
--
-- We use @Seq@ here so we can efficiently sonc, search from the right, and
-- concatenate. Unlike @[]@ (fast view) or @DList@ (fast build), it gives us
-- both fast build and view. And we don't have to think in terms of reversed
-- lists.
newtype Sub = Sub (Seq (Name, Term))

-- @lookup_S@ in the paper
lookupSub :: Name -> Sub -> Maybe Term
lookupSub name (Sub seq') = go seq'
  where
    go :: Seq (Name, Term) -> Maybe Term
    go Empty = Nothing
    go (rest :|> (name', term))
      | name' == name = Just term
      | otherwise     = go rest

-- @subst@ in the paper
-- | The application of an explicit substitution, theta, to a term.
substitute :: Sub -> Term -> Term
substitute theta var@(Var name) =
  case lookupSub name theta of
    Just e -> e
    Nothing -> var
substitute thetaL@(Sub seqL) (Abs (Sub seqR) var ty body) =
    Abs theta var ty body
  where
    theta = Sub $ seqL >< fmap (fmap (substitute thetaL)) seqR
substitute theta (App t0 t1) =
  App (substitute theta t0) (substitute theta t1)

-- @lookup_E@ in the paper
--lookupEnv ::
