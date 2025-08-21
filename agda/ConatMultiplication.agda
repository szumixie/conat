{-# OPTIONS --cubical --guardedness --no-postfix-projections #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe using (Maybe; nothing; just)

record ℕ∞ : Type where
  coinductive
  field
    pred : Maybe ℕ∞
open ℕ∞ public

record NExpr : Type
data Expr : Type

record NExpr where
  coinductive
  field pred : Maybe Expr

open NExpr public

infixl 6 _`+_
data Expr where
  embedℕ∞ : ℕ∞ → Expr
  embed : NExpr → Expr
  _`+_ : Expr → Expr → Expr

infixl 7 _`×_
_`×_ : ℕ∞ → ℕ∞ → NExpr
`×-match : Maybe ℕ∞ → ℕ∞ → Maybe ℕ∞ → Maybe Expr

pred (x `× y) = `×-match (pred x) y (pred y)
`×-match nothing    y y'         = nothing
`×-match (just x')  y nothing    = nothing
`×-match (just x')  y (just y')  =
  just (embedℕ∞ y' `+ embed (x' `× y))

predᴱ : Expr → Maybe Expr
predᴱ-embedℕ∞-match : Maybe ℕ∞ → Maybe Expr
predᴱ-+-match : Maybe Expr → Expr → Maybe Expr

predᴱ (embedℕ∞ x)  = predᴱ-embedℕ∞-match (pred x)
predᴱ (embed x)    = pred x
predᴱ (x `+ y)     = predᴱ-+-match (predᴱ x) y

predᴱ-embedℕ∞-match nothing    = nothing
predᴱ-embedℕ∞-match (just x')  = just (embedℕ∞ x')

predᴱ-+-match nothing    y = predᴱ y
predᴱ-+-match (just x')  y = just (x' `+ y)

interp : Expr → ℕ∞
interp-match : Maybe Expr → Maybe ℕ∞

pred (interp x) = interp-match (predᴱ x)
interp-match nothing    = nothing
interp-match (just x')  = just (interp x')

_×_ : ℕ∞ → ℕ∞ → ℕ∞
x × y = interp (embed (x `× y))
