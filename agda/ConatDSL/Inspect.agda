{-# OPTIONS --safe --cubical #-}

module ConatDSL.Inspect where

open import Agda.Primitive
open import Cubical.Foundations.Prelude

infix 50 Reveal_app_is_
record Reveal_app_is_ {i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x)(x : A)(y : B x) : Type (i ⊔ j) where
  constructor reveal
  field
    equality : f x ≡ y

open Reveal_app_is_ public

inspect : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x)(x : A) → Reveal f app x is f x
inspect f x = reveal refl
