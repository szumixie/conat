{-# OPTIONS --safe --guardedness --cubical #-}

module ConatLib2.Type where

open import Cubical.Data.Maybe

record ℕ∞ : Set where
  coinductive
  constructor unpred
  field
    pred : Maybe ℕ∞

open ℕ∞ public

∞ : ℕ∞
pred ∞ = just ∞
