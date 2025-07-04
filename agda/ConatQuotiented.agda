{-# OPTIONS
  --safe
  --cubical
  --guardedness
  --no-import-sorts
  --hidden-argument-puns #-}

module ConatQuotiented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)
open import Cubical.Foundations.Univalence using (ua→)
open import Cubical.Foundations.HLevels
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
  using
    ( Maybe; nothing; just;
      isOfHLevelMaybe; just-inj; ¬nothing≡just; ¬just≡nothing)

-- exponential commutative semiring + a bit more
record ConatStr (A : Type) : Type where
  infixl 6 _+_
  infixl 7 _*_
  field
    isSetA : isSet A

    _+_ : A → A → A
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm : ∀ x y → x + y ≡ y + x

    zero : A
    +-idₗ : ∀ x → zero + x ≡ x

    _*_ : A → A → A
    *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-comm : ∀ x y → x * y ≡ y * x

    one : A
    *-idₗ : ∀ x → one * x ≡ x

    *-distₗ-+ : ∀ x y z → (x + y) * z ≡ x * z + y * z
    *-annihₗ : ∀ x → zero * x ≡ zero

  suc : A → A
  suc = one +_

  infixr 8 _^_
  field
    _^_ : A → A → A
    ^-assocᵣ-* : ∀ x y z → x ^ (y * z) ≡ (x ^ z) ^ y
    ^-idᵣ : ∀ x → x ^ one ≡ x

    ^-distᵣ-+ : ∀ x y z → x ^ (y + z) ≡ x ^ z * x ^ y
    ^-annihᵣ : ∀ x → x ^ zero ≡ one

    ^-distₗ-* : ∀ x y z → (x * y) ^ z ≡ x ^ z * y ^ z
    ^-annihₗ : ∀ x → one ^ x ≡ one

    -- block x y = ∑_(0≤i<y) x*(1+x)^i = (1+x)^y - 1
    -- e.g.: block 9 3 = 9*10^0 + 9*10^1 + 9*10^2 = 10^3 - 1 = 999
    block : A → A → A
    block-assocᵣ-* : ∀ x y z → block x (y * z) ≡ block (block x z) y
    block-idᵣ : ∀ x → block x one ≡ x

    block-distᵣ-+ :
      ∀ x y z → block x (y + z) ≡ block x y + block x z * suc x ^ y
    block-annihᵣ : ∀ x → block x zero ≡ zero

    block-distₗ-* :
      ∀ x y z → block (y + x * suc y) z ≡ block y z + block x z * suc y ^ z
    block-annihₗ : ∀ x → block zero x ≡ zero

    ^-sucₗ : ∀ x y → suc x ^ y ≡ suc (block x y)

    inf : A
    +-annihₗ : ∀ x → inf + x ≡ inf
    block-infᵣ : ∀ x → block (suc x) inf ≡ inf

  module ConatReasoning where
    infixl 6 _⟩+⟨_
    _⟩+⟨_ : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x + y ≡ x' + y'
    p ⟩+⟨ q = cong₂ _+_ p q

    +-idᵣ : ∀ x → x + zero ≡ x
    +-idᵣ x =
      x + zero ≡⟨ +-comm _ _ ⟩
      zero + x ≡⟨ +-idₗ _ ⟩
      x        ∎

    module _ {a x y z} (p : x + y ≡ z) where
      +-pullᵣ : a + x + y ≡ a + z
      +-pullᵣ =
        a + x + y   ≡⟨ +-assoc _ _ _ ⟩
        a + (x + y) ≡⟨ refl ⟩+⟨ p ⟩
        a + z       ∎

    module _ {a x y z} (p : x ≡ y + z) where
      +-pushᵣ : a + x ≡ a + y + z
      +-pushᵣ = sym (+-pullᵣ (sym p))

    module _ {a x} (p : zero ≡ x) where
      +-introₗ : a ≡ x + a
      +-introₗ =
        a        ≡⟨ sym (+-idₗ _) ⟩
        zero + a ≡⟨ p ⟩+⟨ refl ⟩
        x + a    ∎

      +-introᵣ : a ≡ a + x
      +-introᵣ =
        a        ≡⟨ sym (+-idᵣ _) ⟩
        a + zero ≡⟨ refl ⟩+⟨ p ⟩
        a + x    ∎

    module _ {a x} (p : x ≡ zero) where
      +-elimₗ : x + a ≡ a
      +-elimₗ = sym (+-introₗ (sym p))

      +-elimᵣ : a + x ≡ a
      +-elimᵣ = sym (+-introᵣ (sym p))

    module _ {a x y z w} (p : x + y ≡ z + w) where
      +-extendᵣ : a + x + y ≡ a + z + w
      +-extendᵣ =
        a + x + y   ≡⟨ +-assoc _ _ _ ⟩
        a + (x + y) ≡⟨ refl ⟩+⟨ p ⟩
        a + (z + w) ≡⟨ sym (+-assoc _ _ _) ⟩
        a + z + w   ∎

    +-sucₗ : ∀ x y → suc x + y ≡ suc (x + y)
    +-sucₗ x y = +-assoc _ _ _

    +-sucᵣ : ∀ x y → x + suc y ≡ suc (x + y)
    +-sucᵣ x y =
      x + suc y   ≡⟨ +-comm _ _ ⟩
      suc y + x   ≡⟨ +-sucₗ _ _ ⟩
      suc (y + x) ≡⟨ cong suc (+-comm _ _) ⟩
      suc (x + y) ∎

    infixl 7 _⟩*⟨_
    _⟩*⟨_ : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x * y ≡ x' * y'
    p ⟩*⟨ q = cong₂ _*_ p q

    *-idᵣ : ∀ x → x * one ≡ x
    *-idᵣ x =
      x * one ≡⟨ *-comm _ _ ⟩
      one * x ≡⟨ *-idₗ _ ⟩
      x       ∎

    module _ {a x y z} (p : x * y ≡ z) where
      *-pullᵣ : a * x * y ≡ a * z
      *-pullᵣ =
        a * x * y   ≡⟨ *-assoc _ _ _ ⟩
        a * (x * y) ≡⟨ refl ⟩*⟨ p ⟩
        a * z       ∎

    module _ {a x y z} (p : x ≡ y * z) where
      *-pushᵣ : a * x ≡ a * y * z
      *-pushᵣ = sym (*-pullᵣ (sym p))

    module _ {a x} (p : one ≡ x) where
      *-introᵣ : a ≡ a * x
      *-introᵣ =
        a       ≡⟨ sym (*-idᵣ _) ⟩
        a * one ≡⟨ refl ⟩*⟨ p ⟩
        a * x   ∎

    module _ {a x} (p : x ≡ one) where
      *-elimᵣ : a * x ≡ a
      *-elimᵣ = sym (*-introᵣ (sym p))

    module _ {a x y z w} (p : x * y ≡ z * w) where
      *-extendᵣ : a * x * y ≡ a * z * w
      *-extendᵣ =
        a * x * y   ≡⟨ *-assoc _ _ _ ⟩
        a * (x * y) ≡⟨ refl ⟩*⟨ p ⟩
        a * (z * w) ≡⟨ sym (*-assoc _ _ _) ⟩
        a * z * w   ∎

    *-annihᵣ : ∀ x → x * zero ≡ zero
    *-annihᵣ x =
      x * zero ≡⟨ *-comm _ _ ⟩
      zero * x ≡⟨ *-annihₗ _ ⟩
      zero     ∎

    *-sucₗ : ∀ x y → suc x * y ≡ y + x * y
    *-sucₗ x y =
      (one + x) * y   ≡⟨ *-distₗ-+ _ _ _ ⟩
      one * y + x * y ≡⟨ *-idₗ _ ⟩+⟨ refl ⟩
      y + x * y       ∎

    *-sucᵣ : ∀ x y → x * suc y ≡ x + x * y
    *-sucᵣ x y =
      x * suc y ≡⟨ *-comm _ _ ⟩
      suc y * x ≡⟨ *-sucₗ _ _ ⟩
      x + y * x ≡⟨ refl ⟩+⟨ *-comm _ _ ⟩
      x + x * y ∎

    one-suc : one ≡ suc zero
    one-suc = sym (+-idᵣ _)

    infixr 8 _⟩^⟨_
    _⟩^⟨_ : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x ^ y ≡ x' ^ y'
    p ⟩^⟨ q = cong₂ _^_ p q

    ^-sucᵣ : ∀ x y → x ^ suc y ≡ x ^ y * x
    ^-sucᵣ x y =
      x ^ (one + y)   ≡⟨ ^-distᵣ-+ _ _ _ ⟩
      x ^ y * x ^ one ≡⟨ refl ⟩*⟨ ^-idᵣ _ ⟩
      x ^ y * x       ∎

    block-sucᵣ : ∀ x y → block x (suc y) ≡ x + block x y * suc x
    block-sucᵣ x y =
      block x (one + y)                     ≡⟨ block-distᵣ-+ _ _ _ ⟩
      block x one + block x y * suc x ^ one ≡⟨ block-idᵣ _ ⟩+⟨ refl ⟩*⟨ ^-idᵣ _ ⟩
      x + block x y * suc x                 ∎

    +-annihᵣ : ∀ x → x + inf ≡ inf
    +-annihᵣ x =
      x + inf ≡⟨ +-comm _ _ ⟩
      inf + x ≡⟨ +-annihₗ _ ⟩
      inf     ∎

    inf-suc : inf ≡ suc inf
    inf-suc =
      inf       ≡⟨ sym (+-annihₗ _) ⟩
      inf + one ≡⟨ +-comm _ _ ⟩
      one + inf ∎

    unpred : Maybe A → A
    unpred nothing = zero
    unpred (just x-1) = suc x-1

record ConatStrPred (A : Type) (pred : A → Maybe A) : Type where
  field
    conatStr : ConatStr A

  open ConatStr conatStr public
  open ConatReasoning

  field
    pred-zero : pred zero ≡ nothing
    pred-suc : ∀ x → pred (suc x) ≡ just x
    unpred-pred : ∀ x → unpred (pred x) ≡ x

-- embedded language of Conat expressions
-- based on Nils Anders Danielsson "Beating the Productivity Checker Using Embedded Languages"
-- The difference being that I define a single mixed
-- higher-inductive/coinductive type that includes both the operations
-- and the equations that I want.
module E where
  record NExpr : Type
  data Expr : Type
  suc : Expr → Expr

  -- head normal expressions
  record NExpr where
    coinductive
    field pred : Maybe Expr

  open NExpr public

  infixl 6 _+_
  infixl 7 _*_
  infixr 8 _^_
  data Expr where
    isSetExpr : isSet Expr

    _+_ : Expr → Expr → Expr
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm : ∀ x y → x + y ≡ y + x

    zero : Expr
    +-idₗ : ∀ x → zero + x ≡ x

    _*_ : Expr → Expr → Expr
    *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-comm : ∀ x y → x * y ≡ y * x

    one : Expr
    *-idₗ : ∀ x → one * x ≡ x

    *-distₗ-+ : ∀ x y z → (x + y) * z ≡ x * z + y * z
    *-annihₗ : ∀ x → zero * x ≡ zero

    _^_ : Expr → Expr → Expr
    ^-assocᵣ-* : ∀ x y z → x ^ (y * z) ≡ (x ^ z) ^ y
    ^-idᵣ : ∀ x → x ^ one ≡ x

    ^-distᵣ-+ : ∀ x y z → x ^ (y + z) ≡ x ^ z * x ^ y
    ^-annihᵣ : ∀ x → x ^ zero ≡ one

    ^-distₗ-* : ∀ x y z → (x * y) ^ z ≡ x ^ z * y ^ z
    ^-annihₗ : ∀ x → one ^ x ≡ one

    -- block x y = ∑_(0≤i<y) x*(1+x)^i = (1+x)^y - 1
    -- e.g.: block 9 3 = 9*10^0 + 9*10^1 + 9*10^2 = 10^3 - 1 = 999
    -- for defining the predecessor of exponentiation
    block : Expr → Expr → Expr
    block-assocᵣ-* : ∀ x y z → block x (y * z) ≡ block (block x z) y
    block-idᵣ : ∀ x → block x one ≡ x

    block-distᵣ-+ :
      ∀ x y z → block x (y + z) ≡ block x y + block x z * suc x ^ y
    block-annihᵣ : ∀ x → block x zero ≡ zero

    block-distₗ-* :
      ∀ x y z → block (y + x * suc y) z ≡ block y z + block x z * suc y ^ z
    block-annihₗ : ∀ x → block zero x ≡ zero

    ^-sucₗ : ∀ x y → suc x ^ y ≡ suc (block x y)

    inf : Expr
    +-annihₗ : ∀ x → inf + x ≡ inf
    block-infᵣ : ∀ x → block (suc x) inf ≡ inf

    -- needed because hcomp doesn't preserve guardedness
    trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z

    embed : NExpr → Expr
    embed-zero : ∀ x → x .pred ≡ nothing → embed x ≡ zero
    embed-suc : ∀ x x-1 → x .pred ≡ just x-1 → embed x ≡ suc x-1

  suc = one +_

  conatStrExpr : ConatStr Expr
  conatStrExpr = record{ isSetA = isSetExpr; Expr }

  open ConatStr.ConatReasoning conatStrExpr

  data IsPred : Maybe Expr → Expr → Type where
    nothing : IsPred nothing zero
    just : ∀ x-1 → IsPred (just x-1) (suc x-1)

  isPropIsPred-zero :
    ∀ {x-1 x} (p : nothing ≡ x-1) (q : zero ≡ x) r →
    PathP (λ i → IsPred (p i) (q i)) nothing r
  isPropIsPred-zero p q nothing =
    subst2 (λ e₁ e₂ → PathP (λ i → IsPred (e₁ i) (e₂ i)) nothing nothing)
      (isOfHLevelMaybe 0 isSetExpr _ _ refl p)
      (isSetExpr _ _ refl q)
      refl
  isPropIsPred-zero p q (just x-1) = ⊥.rec (¬nothing≡just p)

  isPropIsPred-suc :
    ∀ {x-1 x} x-1′ (p : just x-1′ ≡ x-1) (q : suc x-1′ ≡ x) r →
    PathP (λ i → IsPred (p i) (q i)) (just x-1′) r
  isPropIsPred-suc x-1′ p q nothing = ⊥.rec (¬just≡nothing p)
  isPropIsPred-suc x-1′ p q (just x-1) =
    subst2 (λ e₁ e₂ → PathP (λ i → IsPred (e₁ i) (e₂ i)) (just x-1′) (just x-1))
      (isOfHLevelMaybe 0 isSetExpr _ _ (cong just (just-inj _ _ p)) p)
      (isSetExpr _ _ (cong suc (just-inj _ _ p)) q)
      (cong IsPred.just (just-inj _ _ p))

  isPropIsPred : ∀ x-1 x → isProp (IsPred x-1 x)
  isPropIsPred _ _ nothing q = isPropIsPred-zero refl refl q
  isPropIsPred _ _ (just x-1) q = isPropIsPred-suc x-1 refl refl q

  -- defining predecessor on expressions inductively
  -- below I define the motive and the methods

  record Pred (x : Expr) : Type where
    field
      pred : Maybe Expr
      isPred : IsPred pred x

  open Pred
  unquoteDecl PredIsoΣ = declareRecordIsoΣ PredIsoΣ (quote Pred)

  Pred-path :
    ∀ {x y} {p : x ≡ y} {xᴾ yᴾ} →
    xᴾ .pred ≡ yᴾ .pred → PathP (λ i → Pred (p i)) xᴾ yᴾ
  Pred-path q i .pred = q i
  Pred-path {p} {xᴾ} {yᴾ} q i .isPred =
    isProp→PathP (λ i → isPropIsPred (q i) (p i)) (xᴾ .isPred) (yᴾ .isPred) i

  isSetPred : ∀ x → isSet (Pred x)
  isSetPred x =
    isOfHLevelRetractFromIso 2 PredIsoΣ
      (isSetΣ (isOfHLevelMaybe 0 isSetExpr) λ x-1 →
        isProp→isSet (isPropIsPred _ _))

  +-pred : Maybe Expr → Expr → Maybe Expr → Maybe Expr
  +-pred nothing y y-1 = y-1
  +-pred (just x-1) y y-1 = just (x-1 + y)

  +-isPred :
    ∀ {x x-1 y y-1} →
    IsPred x-1 x → IsPred y-1 y → IsPred (+-pred x-1 y y-1) (x + y)
  +-isPred {y} nothing p = subst (IsPred _) (sym (+-idₗ _)) p
  +-isPred {y} (just x-1) p =
    subst (IsPred _) (sym (+-sucₗ _ _)) (just (x-1 + y))

  infixl 6 _+ᴾ_
  _+ᴾ_ : ∀ {x y} → Pred x → Pred y → Pred (x + y)
  _+ᴾ_ {y} xᴾ yᴾ .pred = +-pred (xᴾ .pred) y (yᴾ .pred)
  (xᴾ +ᴾ yᴾ) .isPred = +-isPred (xᴾ .isPred) (yᴾ .isPred)

  +-assoc-pred :
    ∀ x-1 y y-1 z z-1 →
    +-pred (+-pred x-1 y y-1) z z-1 ≡ +-pred x-1 (y + z) (+-pred y-1 z z-1)
  +-assoc-pred nothing y y-1 z z-1 = refl
  +-assoc-pred (just x-1) y y-1 z z-1 = congS just (+-assoc _ _ _)

  +-assocᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (+-assoc x y z i)) ((xᴾ +ᴾ yᴾ) +ᴾ zᴾ) (xᴾ +ᴾ (yᴾ +ᴾ zᴾ))
  +-assocᴾ {y} {z} xᴾ yᴾ zᴾ =
    Pred-path (+-assoc-pred (xᴾ .pred) y (yᴾ .pred) z (zᴾ .pred))

  +-comm-pred :
    ∀ {x x-1 y y-1} → IsPred x-1 x → IsPred y-1 y →
    +-pred x-1 y y-1 ≡ +-pred y-1 x x-1
  +-comm-pred nothing nothing = refl
  +-comm-pred nothing (just y-1) = congS just (sym (+-idᵣ _))
  +-comm-pred (just x-1) nothing = congS just (+-idᵣ _)
  +-comm-pred (just x-1) (just y-1) =
    congS just
      ( x-1 + suc y-1   ≡⟨ +-sucᵣ _ _ ⟩
        suc (x-1 + y-1) ≡⟨ cong suc (+-comm _ _) ⟩
        suc (y-1 + x-1) ≡⟨ sym (+-sucᵣ _ _) ⟩
        y-1 + suc x-1   ∎)

  +-commᴾ :
    ∀ {x y} xᴾ yᴾ → PathP (λ i → Pred (+-comm x y i)) (xᴾ +ᴾ yᴾ) (yᴾ +ᴾ xᴾ)
  +-commᴾ xᴾ yᴾ = Pred-path (+-comm-pred (xᴾ .isPred) (yᴾ .isPred))

  zeroᴾ : Pred zero
  zeroᴾ .pred = nothing
  zeroᴾ .isPred = nothing

  +-idₗᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (+-idₗ x i)) (zeroᴾ +ᴾ xᴾ) xᴾ
  +-idₗᴾ xᴾ = Pred-path refl

  *-pred : Maybe Expr → Expr → Maybe Expr → Maybe Expr
  *-pred nothing y y-1 = nothing
  *-pred (just x-1) y nothing = nothing
  *-pred (just x-1) y (just y-1) = just (y-1 + x-1 * y)

  *-isPred :
    ∀ {x x-1 y y-1} →
    IsPred x-1 x → IsPred y-1 y → IsPred (*-pred x-1 y y-1) (x * y)
  *-isPred nothing p = subst (IsPred _) (sym (*-annihₗ _)) nothing
  *-isPred (just x-1) nothing = subst (IsPred _) (sym (*-annihᵣ _)) nothing
  *-isPred {y} (just x-1) (just y-1) =
    subst (IsPred _)
      ( suc (y-1 + x-1 * y) ≡⟨ sym (+-sucₗ _ _) ⟩
        suc y-1 + x-1 * y   ≡⟨⟩
        y + x-1 * y         ≡⟨ sym (*-sucₗ _ _) ⟩
        suc x-1 * y         ∎)
      (just (y-1 + x-1 * y))

  infixl 7 _*ᴾ_
  _*ᴾ_ : ∀ {x y} → Pred x → Pred y → Pred (x * y)
  _*ᴾ_ {y} xᴾ yᴾ .pred = *-pred (xᴾ .pred) y (yᴾ .pred)
  (xᴾ *ᴾ yᴾ) .isPred = *-isPred (xᴾ .isPred) (yᴾ .isPred)

  *-assoc-pred :
    ∀ x-1 y y-1 z z-1 →
    *-pred (*-pred x-1 y y-1) z z-1 ≡ *-pred x-1 (y * z) (*-pred y-1 z z-1)
  *-assoc-pred nothing y y-1 z z-1 = refl
  *-assoc-pred (just x-1) y nothing z z-1 = refl
  *-assoc-pred (just x-1) y (just y-1) z nothing = refl
  *-assoc-pred (just x-1) y (just y-1) z (just z-1) =
    congS just
      ( z-1 + (y-1 + x-1 * y) * z     ≡⟨ +-pushᵣ (*-distₗ-+ _ _ _) ⟩
        z-1 + y-1 * z + x-1 * y * z   ≡⟨ refl ⟩+⟨ *-assoc _ _ _ ⟩
        z-1 + y-1 * z + x-1 * (y * z) ∎)

  *-assocᴾ : ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (*-assoc x y z i)) ((xᴾ *ᴾ yᴾ) *ᴾ zᴾ) (xᴾ *ᴾ (yᴾ *ᴾ zᴾ))
  *-assocᴾ {x} {y} {z} xᴾ yᴾ zᴾ =
    Pred-path (*-assoc-pred (xᴾ .pred) y (yᴾ .pred) z (zᴾ .pred))

  *-comm-pred :
    ∀ {x x-1 y y-1} → IsPred x-1 x → IsPred y-1 y →
    *-pred x-1 y y-1 ≡ *-pred y-1 x x-1
  *-comm-pred nothing nothing = refl
  *-comm-pred nothing (just y-1) = refl
  *-comm-pred (just x-1) nothing = refl
  *-comm-pred (just x-1) (just y-1) =
    congS just
      ( y-1 + x-1 * suc y-1   ≡⟨ +-pushᵣ (*-sucᵣ _ _) ⟩
        y-1 + x-1 + x-1 * y-1 ≡⟨ +-comm _ _ ⟩+⟨ *-comm _ _ ⟩
        x-1 + y-1 + y-1 * x-1 ≡⟨ +-pullᵣ (sym (*-sucᵣ _ _)) ⟩
        x-1 + y-1 * suc x-1 ∎)

  *-commᴾ :
    ∀ {x y} xᴾ yᴾ → PathP (λ i → Pred (*-comm x y i)) (xᴾ *ᴾ yᴾ) (yᴾ *ᴾ xᴾ)
  *-commᴾ xᴾ yᴾ = Pred-path (*-comm-pred (xᴾ .isPred) (yᴾ .isPred))

  oneᴾ : Pred one
  oneᴾ .pred = just zero
  oneᴾ .isPred = subst (IsPred _) (sym one-suc) (just zero)

  *-idₗ-pred : ∀ x x-1 → *-pred (just zero) x x-1 ≡ x-1
  *-idₗ-pred x nothing = refl
  *-idₗ-pred x (just x-1) = congS just (+-elimᵣ (*-annihₗ _))

  *-idₗᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (*-idₗ x i)) (oneᴾ *ᴾ xᴾ) xᴾ
  *-idₗᴾ {x} xᴾ = Pred-path (*-idₗ-pred x (xᴾ .pred))

  *-distₗ-+-pred :
    ∀ x-1 y y-1 z z-1 →
    *-pred (+-pred x-1 y y-1) z z-1 ≡
    +-pred (*-pred x-1 z z-1) (y * z) (*-pred y-1 z z-1)
  *-distₗ-+-pred nothing y y-1 z z-1 = refl
  *-distₗ-+-pred (just x) y y-1 z (just z-1) =
    congS just (+-pushᵣ (*-distₗ-+ _ _ _))
  *-distₗ-+-pred (just x) y nothing z nothing = refl
  *-distₗ-+-pred (just x) y (just y-1) z nothing = refl

  *-distₗ-+ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (*-distₗ-+ x y z i))
      ((xᴾ +ᴾ yᴾ) *ᴾ zᴾ) (xᴾ *ᴾ zᴾ +ᴾ yᴾ *ᴾ zᴾ)
  *-distₗ-+ᴾ {y} {z} xᴾ yᴾ zᴾ =
    Pred-path (*-distₗ-+-pred (xᴾ .pred) y (yᴾ .pred) z (zᴾ .pred))

  *-annihₗᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (*-annihₗ x i)) (zeroᴾ *ᴾ xᴾ) zeroᴾ
  *-annihₗᴾ xᴾ = Pred-path refl

  sucᴾ : ∀ {x} → Pred x → Pred (suc x)
  sucᴾ = oneᴾ +ᴾ_

  ^-pred : Maybe Expr → Expr → Maybe Expr → Maybe Expr
  ^-pred x-1 y nothing = just zero
  ^-pred nothing y (just y-1) = nothing
  ^-pred (just x-1) y (just y-1) = just (block x-1 y)

  ^-isPred :
    ∀ {x x-1 y y-1} →
    IsPred x-1 x → IsPred y-1 y → IsPred (^-pred x-1 y y-1) (x ^ y)
  ^-isPred {x} p nothing =
    subst (IsPred _)
      ( suc zero ≡⟨ sym one-suc ⟩
        one      ≡⟨ sym (^-annihᵣ _) ⟩
        x ^ zero ∎)
      (just zero)
  ^-isPred nothing (just y-1) =
    subst (IsPred _)
      ( zero              ≡⟨ sym (*-annihᵣ _) ⟩
        zero ^ y-1 * zero ≡⟨ sym (^-sucᵣ _ _) ⟩
        zero ^ suc y-1    ∎)
      nothing
  ^-isPred {y} (just x-1) (just y-1) =
    subst (IsPred _) (sym (^-sucₗ _ _)) (just (block x-1 y))

  infixr 8 _^ᴾ_
  _^ᴾ_ : ∀ {x y} → Pred x → Pred y → Pred (x ^ y)
  _^ᴾ_ {y} xᴾ yᴾ .pred = ^-pred (xᴾ .pred) y (yᴾ .pred)
  (xᴾ ^ᴾ yᴾ) .isPred = ^-isPred (xᴾ .isPred) (yᴾ .isPred)

  ^-assocᵣ-*-pred :
    ∀ x-1 y y-1 z z-1 →
    ^-pred x-1 (y * z) (*-pred y-1 z z-1) ≡ ^-pred (^-pred x-1 z z-1) y y-1
  ^-assocᵣ-*-pred x-1 y nothing z z-1 = refl
  ^-assocᵣ-*-pred x-1 y (just y-1) z nothing = congS just (sym (block-annihₗ _))
  ^-assocᵣ-*-pred nothing y (just y-1) z (just z-1) = refl
  ^-assocᵣ-*-pred (just x-1) y (just y-1) z (just z-1) =
    congS just (block-assocᵣ-* _ _ _)

  ^-assocᵣ-*ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (^-assocᵣ-* x y z i))
      (xᴾ ^ᴾ (yᴾ *ᴾ zᴾ)) ((xᴾ ^ᴾ zᴾ) ^ᴾ yᴾ)
  ^-assocᵣ-*ᴾ {x} {y} {z} xᴾ yᴾ zᴾ =
    Pred-path (^-assocᵣ-*-pred (xᴾ .pred) y (yᴾ .pred) z (zᴾ .pred))

  ^-idᵣ-pred : ∀ x-1 → ^-pred x-1 one (just zero) ≡ x-1
  ^-idᵣ-pred nothing = refl
  ^-idᵣ-pred (just x-1) = congS just (block-idᵣ _)

  ^-idᵣᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (^-idᵣ x i)) (xᴾ ^ᴾ oneᴾ) xᴾ
  ^-idᵣᴾ xᴾ = Pred-path (^-idᵣ-pred (xᴾ .pred))

  ^-distᵣ-+-pred :
    ∀ {x x-1 y y-1 z z-1} → IsPred x-1 x → IsPred y-1 y → IsPred z-1 z →
    ^-pred x-1 (y + z) (+-pred y-1 z z-1) ≡
    *-pred (^-pred x-1 z z-1) (x ^ y) (^-pred x-1 y y-1)
  ^-distᵣ-+-pred p nothing nothing =
    congS just (+-introᵣ (sym (*-annihₗ _)))
  ^-distᵣ-+-pred nothing nothing (just z-1) = refl
  ^-distᵣ-+-pred {x} {z} (just x-1) nothing (just z-1) =
    congS just
      ( block x-1 (zero + z)          ≡⟨ cong₂ block refl (+-idₗ _) ⟩
        block x-1 z                   ≡⟨ *-introᵣ (sym (^-annihᵣ _)) ⟩
        block x-1 z * x ^ zero        ≡⟨ sym (+-idₗ _) ⟩
        zero + block x-1 z * x ^ zero ∎)
  ^-distᵣ-+-pred nothing (just y-1) nothing = refl
  ^-distᵣ-+-pred nothing (just y-1) (just x-1) = refl
  ^-distᵣ-+-pred {x} {y} (just x-1) (just y-1) nothing =
    congS just
      ( block x-1 (y + zero)       ≡⟨ cong₂ block refl (+-idᵣ _) ⟩
        block x-1 y                ≡⟨ +-introᵣ (sym (*-annihₗ _)) ⟩
        block x-1 y + zero * x ^ y ∎)
  ^-distᵣ-+-pred (just x-1) (just y-1) (just z-1) =
    congS just (block-distᵣ-+ _ _ _)

  ^-distᵣ-+ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (^-distᵣ-+ x y z i))
      (xᴾ ^ᴾ (yᴾ +ᴾ zᴾ)) (xᴾ ^ᴾ zᴾ *ᴾ xᴾ ^ᴾ yᴾ)
  ^-distᵣ-+ᴾ xᴾ yᴾ zᴾ =
    Pred-path (^-distᵣ-+-pred (xᴾ .isPred) (yᴾ .isPred) (zᴾ .isPred))

  ^-annihᵣᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (^-annihᵣ x i)) (xᴾ ^ᴾ zeroᴾ) oneᴾ
  ^-annihᵣᴾ xᴾ = Pred-path refl

  ^-distₗ-*-pred :
    ∀ {y y-1} x-1 → IsPred y-1 y → ∀ z z-1 →
    ^-pred (*-pred x-1 y y-1) z z-1 ≡
    *-pred (^-pred x-1 z z-1) (y ^ z) (^-pred y-1 z z-1)
  ^-distₗ-*-pred x-1 p z nothing = congS just (+-introᵣ (sym (*-annihₗ _)))
  ^-distₗ-*-pred nothing p z (just z-1) = refl
  ^-distₗ-*-pred (just x-1) nothing z (just z-1) = refl
  ^-distₗ-*-pred {y} (just x-1) (just y-1) z (just z-1) =
    congS just (block-distₗ-* _ _ _)

  ^-distₗ-*ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (^-distₗ-* x y z i))
      ((xᴾ *ᴾ yᴾ) ^ᴾ zᴾ) (xᴾ ^ᴾ zᴾ *ᴾ yᴾ ^ᴾ zᴾ)
  ^-distₗ-*ᴾ {z} xᴾ yᴾ zᴾ =
    Pred-path (^-distₗ-*-pred (xᴾ .pred) (yᴾ .isPred) z (zᴾ .pred))

  ^-annihₗ-pred : ∀ x x-1 → ^-pred (just zero) x x-1 ≡ just zero
  ^-annihₗ-pred x nothing = refl
  ^-annihₗ-pred x (just x-1) = congS just (block-annihₗ _)

  ^-annihₗᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (^-annihₗ x i)) (oneᴾ ^ᴾ xᴾ) oneᴾ
  ^-annihₗᴾ {x} xᴾ = Pred-path (^-annihₗ-pred x (xᴾ .pred))

  block-pred : Expr → Maybe Expr → Maybe Expr → Maybe Expr
  block-pred x nothing y-1 = nothing
  block-pred x (just x-1) nothing = nothing
  block-pred x (just x-1) (just y-1) = just (x-1 + block x y-1 * suc x)

  block-isPred :
    ∀ {x x-1 y y-1} → IsPred x-1 x → IsPred y-1 y →
    IsPred (block-pred x x-1 y-1) (block x y)
  block-isPred nothing p = subst (IsPred _) (sym (block-annihₗ _)) nothing
  block-isPred (just x-1) nothing =
    subst (IsPred _) (sym (block-annihᵣ _)) nothing
  block-isPred {x} (just x-1) (just y-1) =
    subst (IsPred _)
      ( suc (x-1 + block x y-1 * suc x) ≡⟨ sym (+-sucₗ _ _) ⟩
        suc x-1 + block x y-1 * suc x   ≡⟨⟩
        x + block x y-1 * suc x         ≡⟨ sym (block-sucᵣ _ _) ⟩
        block x (suc y-1)               ∎)
      (just (x-1 + block x y-1 * suc x))

  blockᴾ : ∀ {x y} → Pred x → Pred y → Pred (block x y)
  blockᴾ {x} xᴾ yᴾ .pred = block-pred x (xᴾ .pred) (yᴾ .pred)
  blockᴾ xᴾ yᴾ .isPred = block-isPred (xᴾ .isPred) (yᴾ .isPred)

  block-assocᵣ-*-pred :
    ∀ {z z-1} x x-1 y-1 → IsPred z-1 z →
    block-pred x x-1 (*-pred y-1 z z-1) ≡
    block-pred (block x z) (block-pred x x-1 z-1) y-1
  block-assocᵣ-*-pred x nothing y-1 p = refl
  block-assocᵣ-*-pred x (just x-1) nothing nothing = refl
  block-assocᵣ-*-pred x (just x-1) nothing (just z-1) = refl
  block-assocᵣ-*-pred x (just x-1) (just y-1) nothing = refl
  block-assocᵣ-*-pred {z} x (just x-1) (just y-1) (just z-1) =
    congS just
      ( x-1 + block x (z-1 + y-1 * z) * suc x                                       ≡⟨ refl ⟩+⟨ block-distᵣ-+ _ _ _ ⟩*⟨ refl ⟩
        x-1 + (block x z-1 + block x (y-1 * z) * suc x ^ z-1) * suc x               ≡⟨ +-pushᵣ (*-distₗ-+ _ _ _) ⟩
        x-1 + block x z-1 * suc x + block x (y-1 * z) * suc x ^ z-1 * suc x         ≡⟨ refl ⟩+⟨ *-pullᵣ (sym (^-sucᵣ _ _)) ⟩
        x-1 + block x z-1 * suc x + block x (y-1 * z) * suc x ^ suc z-1             ≡⟨ refl ⟩+⟨ block-assocᵣ-* _ _ _ ⟩*⟨ ^-sucₗ _ _ ⟩
        x-1 + block x z-1 * suc x + block (block x z) y-1 * suc (block x (suc z-1)) ∎)

  block-assocᵣ-*ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (block-assocᵣ-* x y z i))
      (blockᴾ xᴾ (yᴾ *ᴾ zᴾ)) (blockᴾ (blockᴾ xᴾ zᴾ) yᴾ)
  block-assocᵣ-*ᴾ {x} xᴾ yᴾ zᴾ =
    Pred-path (block-assocᵣ-*-pred x (xᴾ .pred) (yᴾ .pred) (zᴾ .isPred) )

  block-idᵣ-pred : ∀ x x-1 → block-pred x x-1 (just zero) ≡ x-1
  block-idᵣ-pred x nothing = refl
  block-idᵣ-pred x (just x-1) =
    congS just
      ( x-1 + block x zero * suc x ≡⟨ refl ⟩+⟨ block-annihᵣ _ ⟩*⟨ refl ⟩
        x-1 + zero * suc x         ≡⟨ +-elimᵣ (*-annihₗ _) ⟩
        x-1                        ∎)

  block-idᵣᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (block-idᵣ x i)) (blockᴾ xᴾ oneᴾ) xᴾ
  block-idᵣᴾ {x} xᴾ = Pred-path (block-idᵣ-pred x (xᴾ .pred))

  block-distᵣ-+-pred :
    ∀ {y y-1} x x-1 → IsPred y-1 y → ∀ z z-1 →
    block-pred x x-1 (+-pred y-1 z z-1) ≡
    +-pred
      (block-pred x x-1 y-1)
      (block x z * suc x ^ y)
      (*-pred
        (block-pred x x-1 z-1)
        (suc x ^ y)
        (^-pred (just (zero + x)) y y-1))
  block-distᵣ-+-pred x nothing y-1 z z-1 = refl
  block-distᵣ-+-pred x (just x-1) nothing z nothing = refl
  block-distᵣ-+-pred x (just x-1) nothing z (just z-1) =
    congS just
      ( x-1 + block x z-1 * suc x                         ≡⟨ *-introᵣ (sym (^-annihᵣ _)) ⟩
        (x-1 + block x z-1 * suc x) * suc x ^ zero        ≡⟨ sym (+-idₗ _) ⟩
        zero + (x-1 + block x z-1 * suc x) * suc x ^ zero ∎)
  block-distᵣ-+-pred x (just x-1) (just y-1) z z-1 =
    congS just
      ( x-1 + block x (y-1 + z) * suc x                             ≡⟨ refl ⟩+⟨ block-distᵣ-+ _ _ _ ⟩*⟨ refl ⟩
        x-1 + (block x y-1 + block x z * suc x ^ y-1) * suc x       ≡⟨ +-pushᵣ (*-distₗ-+ _ _ _) ⟩
        x-1 + block x y-1 * suc x + block x z * suc x ^ y-1 * suc x ≡⟨ refl ⟩+⟨ *-pullᵣ (sym (^-sucᵣ _ _)) ⟩
        x-1 + block x y-1 * suc x + block x z * suc x ^ suc y-1     ∎)

  block-distᵣ-+ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (block-distᵣ-+ x y z i))
      (blockᴾ xᴾ (yᴾ +ᴾ zᴾ)) (blockᴾ xᴾ yᴾ +ᴾ blockᴾ xᴾ zᴾ *ᴾ sucᴾ xᴾ ^ᴾ yᴾ)
  block-distᵣ-+ᴾ {x} {z} xᴾ yᴾ zᴾ =
    Pred-path (block-distᵣ-+-pred x (xᴾ .pred) (yᴾ .isPred) z (zᴾ .pred))

  block-annihᵣ-pred : ∀ x x-1 → block-pred x x-1 nothing ≡ nothing
  block-annihᵣ-pred x nothing = refl
  block-annihᵣ-pred x (just x-1) = refl

  block-annihᵣᴾ :
    ∀ {x} xᴾ → PathP (λ i → Pred (block-annihᵣ x i)) (blockᴾ xᴾ zeroᴾ) zeroᴾ
  block-annihᵣᴾ {x} xᴾ = Pred-path (block-annihᵣ-pred x (xᴾ .pred))

  block-distₗ-*-pred :
    ∀ {y y-1 z z-1} x x-1 → IsPred y-1 y → IsPred z-1 z →
    block-pred
      (y + x * suc y)
      (+-pred y-1 (x * suc y) (*-pred x-1 (suc y) (just (zero + y))))
      z-1 ≡
    +-pred
      (block-pred y y-1 z-1)
      (block x z * suc y ^ z)
      (*-pred
        (block-pred x x-1 z-1)
        (suc y ^ z)
        (^-pred (just (zero + y)) z z-1))
  block-distₗ-*-pred {y} x x-1 (just y-1) (just z-1) =
    congS just
      ( y-1 + x * suc y + block (y + x * suc y) z-1 * suc (y + x * suc y)                                   ≡⟨ refl ⟩+⟨ refl ⟩*⟨ sym (+-sucₗ _ _) ⟩
        y-1 + x * suc y + block (y + x * suc y) z-1 * (suc y + x * suc y)                                   ≡⟨ refl ⟩+⟨ *-pushᵣ (sym (*-sucₗ _ _)) ⟩
        y-1 + x * suc y + block (y + x * suc y) z-1 * suc x * suc y                                         ≡⟨ refl ⟩+⟨ block-distₗ-* _ _ _ ⟩*⟨ refl ⟩*⟨ refl ⟩
        y-1 + x * suc y + (block y z-1 + block x z-1 * suc y ^ z-1) * suc x * suc y                         ≡⟨ refl ⟩+⟨ (refl ⟩+⟨ refl ⟩*⟨ ^-sucₗ _ _) ⟩*⟨ refl ⟩*⟨ refl ⟩
        y-1 + x * suc y + (block y z-1 + block x z-1 * suc (block y z-1)) * suc x * suc y                   ≡⟨ +-extendᵣ (q _ _ _ _) ⟩
        y-1 + (x + block y z-1 + block y z-1 * x) * suc y + block x z-1 * suc (block y z-1) * suc x * suc y ≡⟨ refl ⟩+⟨ (+-comm _ _ ⟩+⟨ *-comm _ _) ⟩*⟨ refl ⟩+⟨ *-extendᵣ (*-comm _ _) ⟩*⟨ refl ⟩
        y-1 + (block y z-1 + x + x * block y z-1) * suc y + block x z-1 * suc x * suc (block y z-1) * suc y ≡⟨ +-extendᵣ (sym (q _ _ _ _)) ⟩
        y-1 + block y z-1 * suc y + (x + block x z-1 * suc x) * suc (block y z-1) * suc y                   ≡⟨ refl ⟩+⟨ sym (block-sucᵣ _ _) ⟩*⟨ sym (^-sucₗ _ _) ⟩*⟨ refl ⟩
        y-1 + block y z-1 * suc y + block x (suc z-1) * suc y ^ z-1 * suc y                                 ≡⟨ refl ⟩+⟨ *-pullᵣ (sym (^-sucᵣ _ _)) ⟩
        y-1 + block y z-1 * suc y + block x (suc z-1) * suc y ^ suc z-1                                     ∎)
    where
    q :
      ∀ x y z w →
      x * y + (w + z * suc w) * suc x * y ≡
      (x + w + w * x) * y + z * suc w * suc x * y
    q x y z w =
      x * y + (w + z * suc w) * suc x * y               ≡⟨ refl ⟩+⟨ *-assoc _ _ _ ⟩
      x * y + (w + z * suc w) * (suc x * y)             ≡⟨ +-pushᵣ (*-distₗ-+ _ _ _) ⟩
      x * y + w * (suc x * y) + z * suc w * (suc x * y) ≡⟨ refl ⟩+⟨ sym (*-assoc _ _ _) ⟩+⟨ sym (*-assoc _ _ _) ⟩
      x * y + w * suc x * y + z * suc w * suc x * y     ≡⟨ sym (*-distₗ-+ _ _ _) ⟩+⟨ refl ⟩
      (x + w * suc x) * y + z * suc w * suc x * y       ≡⟨ +-pushᵣ (*-sucᵣ _ _) ⟩*⟨ refl ⟩+⟨ refl ⟩
      (x + w + w * x) * y + z * suc w * suc x * y       ∎
  block-distₗ-*-pred x nothing (just y-1) nothing = refl
  block-distₗ-*-pred x (just x-1) (just y-1) nothing = refl
  block-distₗ-*-pred x nothing nothing p = refl
  block-distₗ-*-pred x (just x-1) nothing nothing = refl
  block-distₗ-*-pred {z} x (just x-1) nothing (just z-1) =
    congS just
      ( zero + zero + x-1 * suc zero + block (zero + x * suc zero) z-1 * suc (zero + x * suc zero) ≡⟨ +-elimₗ (+-idₗ _) ⟩+⟨ cong₂ block (+-idₗ _) refl ⟩*⟨ cong suc (+-idₗ _) ⟩
        x-1 * suc zero + block (x * suc zero) z-1 * suc (x * suc zero)                             ≡⟨ *-elimᵣ (sym one-suc) ⟩+⟨ cong₂ block (*-elimᵣ (sym one-suc)) refl ⟩*⟨ cong suc (*-elimᵣ (sym one-suc)) ⟩
        x-1 + block x z-1 * suc x                                                                  ≡⟨ *-introᵣ (sym (^-annihₗ _)) ⟩
        (x-1 + block x z-1 * suc x) * one ^ z                                                      ≡⟨ +-introₗ (sym (block-annihₗ _)) ⟩
        block zero z + (x-1 + block x z-1 * suc x) * one ^ z                                       ≡⟨ cong₂ block (sym (+-idₗ _)) refl ⟩+⟨ refl ⟩*⟨ one-suc ⟩^⟨ refl ⟩
        block (zero + zero) z + (x-1 + block x z-1 * suc x) * suc zero ^ z                         ∎)

  block-distₗ-*ᴾ :
    ∀ {x y z} xᴾ yᴾ zᴾ →
    PathP (λ i → Pred (block-distₗ-* x y z i))
      (blockᴾ (yᴾ +ᴾ xᴾ *ᴾ sucᴾ yᴾ) zᴾ)
      (blockᴾ yᴾ zᴾ +ᴾ blockᴾ xᴾ zᴾ *ᴾ sucᴾ yᴾ ^ᴾ zᴾ)
  block-distₗ-*ᴾ {x} xᴾ yᴾ zᴾ =
    Pred-path (block-distₗ-*-pred x (xᴾ .pred) (yᴾ .isPred) (zᴾ .isPred))

  block-annihₗᴾ :
    ∀ {x} xᴾ → PathP (λ i → Pred (block-annihₗ x i)) (blockᴾ zeroᴾ xᴾ) zeroᴾ
  block-annihₗᴾ xᴾ = Pred-path refl

  ^-sucₗ-pred :
    ∀ {y y-1} x → IsPred y-1 y → ^-pred (just (zero + x)) y y-1 ≡ just (zero + block x y)
  ^-sucₗ-pred x nothing = congS just (+-introᵣ (sym (block-annihᵣ _)))
  ^-sucₗ-pred {y} x (just y-1) =
    congS just
      ( block (zero + x) y ≡⟨ cong₂ block (+-idₗ _) refl ⟩
        block x y          ≡⟨ sym (+-idₗ _) ⟩
        zero + block x y   ∎)

  ^-sucₗᴾ :
    ∀ {x y} xᴾ yᴾ →
    PathP (λ i → Pred (^-sucₗ x y i)) (sucᴾ xᴾ ^ᴾ yᴾ) (sucᴾ (blockᴾ xᴾ yᴾ))
  ^-sucₗᴾ {x} xᴾ yᴾ = Pred-path (^-sucₗ-pred x (yᴾ .isPred))

  infᴾ : Pred inf
  infᴾ .pred = just inf
  infᴾ .isPred = subst (IsPred _) (sym inf-suc) (just inf)

  +-annihₗᴾ : ∀ {x} xᴾ → PathP (λ i → Pred (+-annihₗ x i)) (infᴾ +ᴾ xᴾ) infᴾ
  +-annihₗᴾ xᴾ = Pred-path (congS just (+-annihₗ _))

  block-infᵣᴾ :
    ∀ {x} xᴾ → PathP (λ i → Pred (block-infᵣ x i)) (blockᴾ (sucᴾ xᴾ) infᴾ) infᴾ
  block-infᵣᴾ {x} xᴾ =
    Pred-path
      (congS just
        ( zero + x + block (suc x) inf * suc (suc x) ≡⟨ +-idₗ _ ⟩+⟨ block-infᵣ x ⟩*⟨ refl ⟩
          x + inf * suc (suc x)                      ≡⟨ +-pushᵣ (*-sucᵣ _ _) ⟩
          x + inf + inf * suc x                      ≡⟨ +-annihᵣ _ ⟩+⟨ refl ⟩
          inf + inf * suc x                          ≡⟨ +-annihₗ _ ⟩
          inf                                        ∎))

  transᴾ :
    ∀ {x y z} {p : x ≡ y} {q : y ≡ z} {xᴾ yᴾ zᴾ} →
    PathP (λ i → Pred (p i)) xᴾ yᴾ → PathP (λ i → Pred (q i)) yᴾ zᴾ →
    PathP (λ i → Pred (trans p q i)) xᴾ zᴾ
  transᴾ pᴾ qᴾ = Pred-path ((λ i → pᴾ i .pred) ∙ (λ i → qᴾ i .pred))

  embed-isPred : ∀ x x-1 → x .pred ≡ x-1 → IsPred x-1 (embed x)
  embed-isPred x nothing p = subst (IsPred _) (sym (embed-zero x p)) nothing
  embed-isPred x (just x-1) p =
    subst (IsPred _) (sym (embed-suc x x-1 p)) (just x-1)

  embedᴾ : ∀ x → Pred (embed x)
  embedᴾ x .pred = x .pred
  embedᴾ x .isPred = embed-isPred x (x .pred) refl

  embed-zeroᴾ : ∀ x p → PathP (λ i → Pred (embed-zero x p i)) (embedᴾ x) zeroᴾ
  embed-zeroᴾ x p = Pred-path p

  embed-sucᴾ :
    ∀ {x-1} x x-1ᴾ p →
    PathP (λ i → Pred (embed-suc x x-1 p i)) (embedᴾ x) (sucᴾ x-1ᴾ)
  embed-sucᴾ {x-1} x x-1ᴾ p = Pred-path
    ( x .pred           ≡⟨ p ⟩
      just x-1          ≡⟨ congS just (sym (+-idₗ _)) ⟩
      just (zero + x-1) ∎)

  ⟦_⟧ᴾ : ∀ x → Pred x
  ⟦ isSetExpr x y p q i j ⟧ᴾ =
    isOfHLevel→isOfHLevelDep 2 (λ x → isSetPred x)
      ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ (cong ⟦_⟧ᴾ p) (cong ⟦_⟧ᴾ q) (isSetExpr _ _ _ _) i j

  ⟦ x + y ⟧ᴾ = ⟦ x ⟧ᴾ +ᴾ ⟦ y ⟧ᴾ
  ⟦ +-assoc x y z i ⟧ᴾ = +-assocᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ +-comm x y i ⟧ᴾ = +-commᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ i
  ⟦ zero ⟧ᴾ = zeroᴾ
  ⟦ +-idₗ x i ⟧ᴾ = +-idₗᴾ ⟦ x ⟧ᴾ i

  ⟦ x * y ⟧ᴾ = ⟦ x ⟧ᴾ *ᴾ ⟦ y ⟧ᴾ
  ⟦ *-assoc x y z i ⟧ᴾ = *-assocᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ *-comm x y i ⟧ᴾ = *-commᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ i
  ⟦ one ⟧ᴾ = oneᴾ
  ⟦ *-idₗ x i ⟧ᴾ = *-idₗᴾ ⟦ x ⟧ᴾ i
  ⟦ *-distₗ-+ x y z i ⟧ᴾ = *-distₗ-+ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ *-annihₗ x i ⟧ᴾ = *-annihₗᴾ ⟦ x ⟧ᴾ i

  ⟦ x ^ y ⟧ᴾ = ⟦ x ⟧ᴾ ^ᴾ ⟦ y ⟧ᴾ
  ⟦ ^-assocᵣ-* x y z i ⟧ᴾ = ^-assocᵣ-*ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ ^-idᵣ x i ⟧ᴾ = ^-idᵣᴾ ⟦ x ⟧ᴾ i
  ⟦ ^-distᵣ-+ x y z i ⟧ᴾ = ^-distᵣ-+ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ ^-annihᵣ x i ⟧ᴾ = ^-annihᵣᴾ ⟦ x ⟧ᴾ i
  ⟦ ^-distₗ-* x y z i ⟧ᴾ = ^-distₗ-*ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ ^-annihₗ x i ⟧ᴾ = ^-annihₗᴾ ⟦ x ⟧ᴾ i

  ⟦ block x y ⟧ᴾ = blockᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ
  ⟦ block-assocᵣ-* x y z i ⟧ᴾ = block-assocᵣ-*ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ block-idᵣ x i ⟧ᴾ = block-idᵣᴾ ⟦ x ⟧ᴾ i
  ⟦ block-distᵣ-+ x y z i ⟧ᴾ = block-distᵣ-+ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ block-annihᵣ x i ⟧ᴾ = block-annihᵣᴾ ⟦ x ⟧ᴾ i
  ⟦ block-distₗ-* x y z i ⟧ᴾ = block-distₗ-*ᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ ⟦ z ⟧ᴾ i
  ⟦ block-annihₗ x i ⟧ᴾ = block-annihₗᴾ ⟦ x ⟧ᴾ i
  ⟦ ^-sucₗ x y i ⟧ᴾ = ^-sucₗᴾ ⟦ x ⟧ᴾ ⟦ y ⟧ᴾ i

  ⟦ inf ⟧ᴾ = infᴾ
  ⟦ +-annihₗ x i ⟧ᴾ = +-annihₗᴾ ⟦ x ⟧ᴾ i
  ⟦ block-infᵣ x i ⟧ᴾ = block-infᵣᴾ ⟦ x ⟧ᴾ i

  ⟦ trans p q i ⟧ᴾ = transᴾ (cong ⟦_⟧ᴾ p) (cong ⟦_⟧ᴾ q) i
  ⟦ embed x ⟧ᴾ = embedᴾ x
  ⟦ embed-zero x p i ⟧ᴾ = embed-zeroᴾ x p i
  ⟦ embed-suc x x-1 p i ⟧ᴾ = embed-sucᴾ x ⟦ x-1 ⟧ᴾ p i

  predᴱ : Expr → Maybe Expr
  predᴱ x = ⟦ x ⟧ᴾ .pred

  isPredᴱ : ∀ x → IsPred (predᴱ x) x
  isPredᴱ x = ⟦ x ⟧ᴾ .isPred

  pred-zero : predᴱ zero ≡ nothing
  pred-zero = refl

  pred-suc : ∀ x → predᴱ (suc x) ≡ just x
  pred-suc x = congS just (+-idₗ _)

  unpred-pred-pred : ∀ {x x-1} → IsPred x-1 x → unpred x-1 ≡ x
  unpred-pred-pred nothing = refl
  unpred-pred-pred (just x-1) = refl

  unpred-pred : ∀ x → unpred (predᴱ x) ≡ x
  unpred-pred x = unpred-pred-pred (isPredᴱ x)

  conatStrPredExpr : ConatStrPred Expr predᴱ
  conatStrPredExpr =
    record
      { conatStr = conatStrExpr;
        pred-zero = pred-zero;
        pred-suc = pred-suc;
        unpred-pred = unpred-pred }

  interp : Expr → NExpr
  interp x .pred = predᴱ x

  interp-embed : ∀ x → interp (embed x) ≡ x
  interp-embed x i .pred = x .pred

  embed-interp : ∀ x → embed (interp x) ≡ x
  embed-interp-pred : ∀ {x x-1} → IsPred x-1 x → embed (interp x) ≡ x

  embed-interp x = embed-interp-pred (isPredᴱ x)
  embed-interp-pred nothing = embed-zero (interp zero) refl
  embed-interp-pred (just x-1) =
    embed-suc (interp (suc x-1)) x-1 (congS just (+-idₗ _))

  ExprIsoNExpr : Iso Expr NExpr
  ExprIsoNExpr = iso interp embed interp-embed embed-interp

open E using (NExpr; Expr; pred; predᴱ; conatStrPredExpr)

record Conat : Type where
  coinductive
  field pred : Maybe Conat

open Conat public

embed : Conat → Expr
embedᴺ : Conat → NExpr
embed-pred : Maybe Conat → Maybe Expr

embed x = E.embed (embedᴺ x)
embedᴺ x .pred = embed-pred (x .pred)
embed-pred nothing = nothing
embed-pred (just x-1) = just (embed x-1)

interp : Expr → Conat
interp-pred : Maybe Expr → Maybe Conat

interp x .pred = interp-pred (predᴱ x)
interp-pred nothing = nothing
interp-pred (just x-1) = just (interp x-1)

interp-embed : ∀ x → interp (embed x) ≡ x
interp-embed-pred : ∀ x-1 → interp-pred (embed-pred x-1) ≡ x-1

interp-embed x i .pred = interp-embed-pred (x .pred) i
interp-embed-pred nothing = refl
interp-embed-pred (just x-1) = cong just (interp-embed x-1)

embed-interp : ∀ x → embed (interp x) ≡ x
embed-interpᴺ : ∀ x → embedᴺ (interp x) ≡ E.interp x
embed-interp-pred : ∀ x-1 → embed-pred (interp-pred x-1) ≡ x-1

embed-interp x = E.trans (cong E.embed (embed-interpᴺ x)) (E.embed-interp x)
embed-interpᴺ x i .pred = embed-interp-pred (predᴱ x) i
embed-interp-pred nothing = refl
embed-interp-pred (just x-1) = cong just (embed-interp x-1)

ExprIsoConat : Iso Expr Conat
ExprIsoConat = iso interp embed interp-embed embed-interp

-- uses univalence, could be done without it with more work
conatStrPredConat : ConatStrPred Conat pred
conatStrPredConat =
  transport
    (cong₂ ConatStrPred
      (isoToPath ExprIsoConat)
      (ua→ λ x → toPathP (subst-Maybe _)))
    conatStrPredExpr
  where
  subst-Maybe :
    ∀ x-1 → subst Maybe (isoToPath ExprIsoConat) x-1 ≡ interp-pred x-1
  subst-Maybe nothing = refl
  subst-Maybe (just x-1) = cong just (transportRefl _)

open ConatStrPred conatStrPredConat
  renaming (isSetA to isSetConat; conatStr to conatStrConat) public
open ConatReasoning public

private
  example : Conat
  example = suc (suc zero) ^ inf

  _ : example ≡ inf
  _ =
    suc (suc zero) ^ inf       ≡⟨ ^-sucₗ _ _ ⟩
    suc (block (suc zero) inf) ≡⟨ cong suc (block-infᵣ _) ⟩
    suc inf                    ≡⟨ sym inf-suc ⟩
    inf                        ∎

  _ : one .pred ≡ just zero
  _ =
    one .pred      ≡⟨ cong pred one-suc ⟩
    suc zero .pred ≡⟨ pred-suc _ ⟩
    just zero      ∎
