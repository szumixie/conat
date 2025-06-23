{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module ConatDirect where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit using (tt) renaming (Unit to ⊤)
import Cubical.Data.Empty as ⊥
open ⊥ using (⊥)
import Cubical.Data.Nat as ℕ renaming (_·_ to _*_)
open ℕ using (ℕ)
open import Cubical.Tactics.NatSolver using (solveℕ!)

data Conat : Type
record Conat₊ : Type

data Conat where
  zero : Conat
  pos : Conat₊ → Conat

record Conat₊ where
  coinductive
  constructor unpred
  field pred : Conat

open Conat₊ public

pos-inj : ∀ {x y} → pos x ≡ pos y → x ≡ y
pos-inj p = cong f p
  where
  f : Conat → Conat₊
  f zero = unpred zero
  f (pos x) = x

pred-inj : ∀ {x y} → x .pred ≡ y .pred → x ≡ y
pred-inj p i .pred = p i

IsZero : Conat → Type
IsZero zero = ⊤
IsZero (pos x) = ⊥

IsPos : Conat → Type
IsPos zero = ⊥
IsPos (pos x) = ⊤

zero≢pos : ∀ {x} → zero ≡ pos x → ⊥
zero≢pos p = subst IsZero p tt

--------------------------------------------------------------------------------
-- Operations on positive Conats

module P where
  data Step (State : Type) : Type where
    zero : Step State
    pos : Conat₊ → Step State
    cont : State → Step State

  -- primitive corecursion / apomorphism
  module Corec (State : Type) (step : State → Step State) where
    corec : State → Conat₊
    corec′ : Step State → Conat

    corec s .pred = corec′ (step s)
    corec′ zero = zero
    corec′ (pos x) = pos x
    corec′ (cont s) = pos (corec s)

  data StepR (State : Conat₊ → Conat₊ → Type) : Conat → Conat → Type where
    zero : StepR State zero zero
    pos : ∀ {x y} → x ≡ y → StepR State (pos x) (pos y)
    cont : ∀ {x y} → State x y → StepR State (pos x) (pos y)

  module Bisim
    (State : Conat₊ → Conat₊ → Type)
    (step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred))
    where
    bisim : ∀ {x y} → State x y → x ≡ y
    bisim′ : ∀ {x y} → StepR State x y → x ≡ y

    bisim s i .pred = bisim′ (step s) i
    bisim′ zero i = zero
    bisim′ (pos p) i = pos (p i)
    bisim′ (cont s) i = pos (bisim s i)

  one : Conat₊
  one = unpred zero

  suc : Conat₊ → Conat₊
  suc x = unpred (pos x)

  suc-inj : ∀ {x y} → suc x ≡ suc y → x ≡ y
  suc-inj p = pos-inj (cong pred p)

  data PredView : Conat₊ → Conat → Type where
    zero : PredView one zero
    pos : ∀ x → PredView (suc x) (pos x)

  predView′ : ∀ x x-1 → x .pred ≡ x-1 → PredView x x-1
  predView′ x zero p =
    subst (λ x → PredView x zero) (pred-inj (sym p)) zero
  predView′ x (pos x-1) p =
    subst (λ x → PredView x (pos x-1)) (pred-inj (sym p)) (pos x-1)

  predView : ∀ x → PredView x (x .pred)
  predView x = predView′ x (x .pred) refl

  infixl 6 _+ₗ_
  _+ₗ_ : ℕ → Conat₊ → Conat₊
  ℕ.zero +ₗ x = x
  ℕ.suc n +ₗ x = suc (n +ₗ x)

  +ₗ-suc : ∀ n x → n +ₗ suc x ≡ suc (n +ₗ x)
  +ₗ-suc ℕ.zero x = refl
  +ₗ-suc (ℕ.suc n) x = cong suc (+ₗ-suc n x)

  fromℕ₊ : ℕ → Conat₊
  fromℕ₊ n = n +ₗ one

  fromℕ₊-inj : ∀ {x y} → fromℕ₊ x ≡ fromℕ₊ y → x ≡ y
  fromℕ₊-inj {ℕ.zero} {ℕ.zero} p = refl
  fromℕ₊-inj {ℕ.zero} {ℕ.suc y} p = ⊥.rec (zero≢pos (cong pred p))
  fromℕ₊-inj {ℕ.suc x} {ℕ.zero} p = ⊥.rec (zero≢pos (cong pred (sym p)))
  fromℕ₊-inj {ℕ.suc x} {ℕ.suc y} p = cong ℕ.suc (fromℕ₊-inj (suc-inj p))

  module inf where
    data State : Type where
      state : State

    step : State → Step State
    step state = cont state

    open Corec State step public

  inf : Conat₊
  inf = inf.corec inf.state

  inf≢fromℕ₊ : ∀ n → inf ≡ fromℕ₊ n → ⊥
  inf≢fromℕ₊ ℕ.zero p = zero≢pos (sym (cong pred p))
  inf≢fromℕ₊ (ℕ.suc n) p = inf≢fromℕ₊ n (pos-inj (cong pred p))

  ------------------------------------------------------------------------------
  -- Addition

  module + where
    {- 4+3:
    1: state 4 3
    2: state 3 3
    3: state 2 3
    4: state 1 3
    5: 3
    6: 2
    7: 1
    -}
    data State : Type where
      state : Conat₊ → Conat₊ → State

    step′ : Conat → Conat₊ → Step State
    step′ (pos x-1) y₀ = cont (state x-1 y₀)
    step′ zero y₀ = pos y₀

    step : State → Step State
    step (state x y₀) = step′ (x .pred) y₀

    open Corec State step public

    corec-fromℕ₊ :
      ∀ x y → corec (state (fromℕ₊ x) (fromℕ₊ y)) ≡ fromℕ₊ (x ℕ.+ ℕ.suc y)
    corec-fromℕ₊ ℕ.zero y = pred-inj refl
    corec-fromℕ₊ (ℕ.suc x) y = pred-inj (cong pos (corec-fromℕ₊ x y))

  infixl 6 _+_
  _+_ : Conat₊ → Conat₊ → Conat₊
  x + y = +.corec (+.state x y)

  +-fromℕ₊ : ∀ x y → fromℕ₊ x + fromℕ₊ y ≡ fromℕ₊ (x ℕ.+ ℕ.suc y)
  +-fromℕ₊ x y = +.corec-fromℕ₊ x y

  module +-assoc where
    data State : Conat₊ → Conat₊ → Type where
      state :
        ∀ x y₀ z₀ →
        State
          (+.corec (+.state (+.corec (+.state x y₀)) z₀))
          (+.corec (+.state x (y₀ + z₀)))

    step′ :
      ∀ x-1 y₀ z₀ →
      StepR State
        (+.corec′ (+.step′ (+.corec′ (+.step′ x-1 y₀)) z₀))
        (+.corec′ (+.step′ x-1 (y₀ + z₀)))
    step′ (pos x-1) y₀ z₀ = cont (state x-1 y₀ z₀)
    step′ zero y₀ z₀ = pos refl

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x y₀ z₀) = step′ (x .pred) y₀ z₀

    open Bisim State step public

  +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  +-assoc x y z = +-assoc.bisim (+-assoc.state x y z)

  module +-comm₂ where
    data State : Conat₊ → Conat₊ → Type where
      {-
        n+1       n+1+y
      /'''''\  /''''''''''\
      ------#-->----------#
      --------->---#------#
               \___/\_____/
                 y    n+1
      -}
      state : ∀ n y → State (n +ₗ suc y) (+.corec (+.state y (n +ₗ one)))

    step′
      : ∀ n {y y-1} → PredView y y-1 →
      StepR State ((n +ₗ suc y) .pred) (+.corec′ (+.step′ y-1 (n +ₗ one)))
    step′ n (pos y-1) =
      subst
        (λ e → StepR State (e .pred) (pos (+.corec (+.state y-1 (n +ₗ one)))))
        (sym (+ₗ-suc n (suc y-1)))
        (cont (state n y-1))
    step′ n zero =
      subst
        (λ e → StepR State (e .pred) (pos (n +ₗ one)))
        (sym (+ₗ-suc n one))
        (pos refl)

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state n y) = step′ n (predView y)

    open Bisim State step public

  module +-comm₁ where
    data State : Conat₊ → Conat₊ → Type where
      {-
             x      n+y
           /'''\/''''''''''\
      ----->---#-----------#
      ----->-----#---------#
      \___/\_____/\________/
        n     y      n+x
      -}
      state :
        ∀ n x y →
        State (+.corec (+.state x (n +ₗ y))) (+.corec (+.state y (n +ₗ x)))

    step′ :
      ∀ n {x x-1 y y-1} → PredView x x-1 → PredView y y-1 →
      StepR State
        (+.corec′ (+.step′ (x .pred) (n +ₗ y)))
        (+.corec′ (+.step′ (y .pred) (n +ₗ x)))
    step′ n (pos x-1) (pos y-1) =
      cont
        (subst2
          (λ e₁ e₂ →
            State (+.corec (+.state x-1 e₁)) (+.corec (+.state y-1 e₂)))
          (sym (+ₗ-suc n y-1))
          (sym (+ₗ-suc n x-1))
          (state (ℕ.suc n) x-1 y-1))
    step′ n zero (pos y-1) = pos (+-comm₂.bisim (+-comm₂.state n y-1))
    step′ n (pos x-1) zero = pos (sym (+-comm₂.bisim (+-comm₂.state n x-1)))
    step′ n zero zero = pos refl

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state n x y) = step′ n (predView x) (predView y)

    open Bisim State step public

  +-comm : ∀ x y → x + y ≡ y + x
  +-comm x y = +-comm₁.bisim (+-comm₁.state ℕ.zero x y)

  module +-annihₗ where
    data State : Conat₊ → Conat₊ → Type where
      state :
        ∀ x₀ →
          State
            (+.corec (+.state (inf.corec inf.state) x₀))
            (inf.corec inf.state)

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x₀) = cont (state x₀)

    open Bisim State step public

  +-annihₗ : ∀ x → inf + x ≡ inf
  +-annihₗ x = +-annihₗ.bisim (+-annihₗ.state x)

  +-oneₗ : ∀ x → one + x ≡ suc x
  +-oneₗ x = pred-inj refl

  +-sucₗ : ∀ x y → suc x + y ≡ suc (x + y)
  +-sucₗ x y = pred-inj refl

  ------------------------------------------------------------------------------
  -- Multiplication

  module * where
    {- 4*3:
    1:  state 4 3 3
    2:  state 4 2 3
    3:  state 4 1 3
    4:  state 3 3 3
    5:  state 3 2 3
    6:  state 3 1 3
    7:  state 2 3 3
    8:  state 2 2 3
    9:  state 2 1 3
    10: state 1 3 3
    11: state 1 2 3
    12: state 1 1 3
    -}
    data State : Type where
      state : Conat₊ → Conat₊ → Conat₊ → State

    step′₂ : Conat → Conat₊ → Step State
    step′₂ (pos x-1) y₀ = cont (state x-1 y₀ y₀)
    step′₂ zero y₀ = zero

    step′₁ : Conat₊ → Conat → Conat₊ → Step State
    step′₁ x (pos y-1) y₀ = cont (state x y-1 y₀)
    step′₁ x zero y₀ = step′₂ (x .pred) y₀

    step : State → Step State
    step (state x y y₀) = step′₁ x (y .pred) y₀

    open Corec State step public

    corec-fromℕ₊ :
      ∀ x y y₀ →
      corec (state (fromℕ₊ x) (fromℕ₊ y) (fromℕ₊ y₀)) ≡
      fromℕ₊ (y ℕ.+ x ℕ.* ℕ.suc y₀)
    corec-fromℕ₊ x (ℕ.suc y) y₀ = pred-inj (cong pos (corec-fromℕ₊ x y y₀))
    corec-fromℕ₊ ℕ.zero ℕ.zero y₀ = pred-inj refl
    corec-fromℕ₊ (ℕ.suc x) ℕ.zero y₀ =
      pred-inj (cong pos (corec-fromℕ₊ x y₀ y₀))

  infixl 7 _*_
  _*_ : Conat₊ → Conat₊ → Conat₊
  x * y = *.corec (*.state x y y)

  *-fromℕ₊ : ∀ x y → fromℕ₊ x * fromℕ₊ y ≡ fromℕ₊ (y ℕ.+ x ℕ.* ℕ.suc y)
  *-fromℕ₊ x y = *.corec-fromℕ₊ x y y

  module *-assoc where
    data State : Conat₊ → Conat₊ → Type where
      state :
        ∀ x y y₀ z z₀ →
        State
          (*.corec (*.state (*.corec (*.state x y y₀)) z z₀))
          (*.corec (*.state x (*.corec (*.state y z z₀)) (y₀ * z₀)))

    step′₃ :
      ∀ x-1 y₀ z₀ →
      StepR State
        (*.corec′ (*.step′₂ (*.corec′ (*.step′₂ x-1 y₀)) z₀))
        (*.corec′ (*.step′₂ x-1 (y₀ * z₀)))
    step′₃ (pos x-1) y₀ z₀ = cont (state x-1 y₀ y₀ z₀ z₀)
    step′₃ zero y₀ z₀ = zero

    step′₂ :
      ∀ x y-1 y₀ z₀ →
      StepR State
        (*.corec′ (*.step′₂ (*.corec′ (*.step′₁ x y-1 y₀)) z₀))
        (*.corec′ (*.step′₁ x (*.corec′ (*.step′₂ y-1 z₀)) (y₀ * z₀)))
    step′₂ x (pos y-1) y₀ z₀ = cont (state x y-1 y₀ z₀ z₀)
    step′₂ x zero y₀ z₀ = step′₃ (x .pred) y₀ z₀

    step′₁ :
      ∀ x y y₀ z-1 z₀ →
      StepR State
        (*.corec′ (*.step′₁ (*.corec (*.state x y y₀)) z-1 z₀))
        (*.corec′ (*.step′₁ x (*.corec′ (*.step′₁ y z-1 z₀)) (y₀ * z₀)))
    step′₁ x y y₀ (pos z-1) z₀ = cont (state x y y₀ z-1 z₀)
    step′₁ x y y₀ zero z₀ = step′₂ x (y .pred) y₀ z₀

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x y y₀ z z₀) = step′₁ x y y₀ (z .pred) z₀

    open Bisim State step public

  *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
  *-assoc x y z = *-assoc.bisim (*-assoc.state x y y z z)

  module *-idₗ where
    data State : Conat₊ → Conat₊ → Type where
      state : ∀ x x₀ → State (*.corec (*.state one x x₀)) x

    step′ : ∀ x-1 x₀ → StepR State (*.corec′ (*.step′₁ one x-1 x₀)) x-1
    step′ (pos x-1) x₀ = cont (state x-1 x₀)
    step′ zero x₀ = zero

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x x₀) = step′ (x .pred) x₀

    open Bisim State step public

  *-idₗ : ∀ x → one * x ≡ x
  *-idₗ x = *-idₗ.bisim (*-idₗ.state x x)

  module *-comm₂ where
    data State : Conat₊ → Conat₊ → Type where
      {-
                                       m+n+1 times
      /'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
                            (1+k)*(m+n+1)+m+y
      /''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''\/'''''''''''''''
                   (1+k)*(m+n+1)+m                       y
      /'''''''''''''''''''''''''''''''''''''''\/'''''''''''''''''''\
      ----------------------------------------->-------------------#-------------...
      -----------#-----------#-----------#----->-----#-----------#-----------#---...
      \__________/\__________/\__________/\___/\_____/\__________/\__________/\_____
         m+n+1       m+n+1       m+n+1      m    n+1     m+n+1       m+n+1
      \__________________________________/\_________________________________________
                   1+k times                        (1+k)*(m+n)+m+y times
      -}
      state :
        ∀ k m n y →
        State
          (*.corec
            (*.state
              (m ℕ.+ n +ₗ one)
              y
              (ℕ.suc k ℕ.* (m ℕ.+ n ℕ.+ 1) ℕ.+ m +ₗ y)))
          (*.corec
            (*.state
              (ℕ.suc k ℕ.* (m ℕ.+ n) ℕ.+ m +ₗ y)
              (n +ₗ one)
              (m ℕ.+ n +ₗ one)))

    step′ :
      ∀ k m n {y y-1} → PredView y y-1 →
      StepR State
        (*.corec′
          (*.step′₁
            (m ℕ.+ n +ₗ one)
            y-1
            (ℕ.suc k ℕ.* (m ℕ.+ n ℕ.+ 1) ℕ.+ m +ₗ y)))
        (*.corec′
          (*.step′₁
            (ℕ.suc k ℕ.* (m ℕ.+ n) ℕ.+ m +ₗ y)
            ((n +ₗ one) .pred)
            (m ℕ.+ n +ₗ one)))
    step′ k m (ℕ.suc n) (pos y-1) =
      cont
        (transport
          (cong₃
            (λ e₁ e₂ e₃ →
              State
                (*.corec (*.state (e₁ +ₗ one) y-1 e₂))
                (*.corec (*.state e₃ (n +ₗ one) (e₁ +ₗ one))))
            p
            ( cong (_+ₗ y-1) q ∙
              sym (+ₗ-suc (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m) y-1))
            ( cong (_+ₗ y-1) r ∙
              sym (+ₗ-suc (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n) ℕ.+ m) y-1)))
          (state k (ℕ.suc m) n y-1))
      where
      p : ℕ.suc m ℕ.+ n ≡ m ℕ.+ ℕ.suc n
      p = solveℕ!
      q :
        ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ n ℕ.+ 1) ℕ.+ ℕ.suc m ≡
        ℕ.suc (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m)
      q = solveℕ!
      r :
        ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ n) ℕ.+ ℕ.suc m ≡
        ℕ.suc (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n) ℕ.+ m)
      r = solveℕ!
    step′ k m ℕ.zero (pos y-1) =
      transport
        (cong₃
          (λ e₁ e₂ e₃ →
            StepR State
              (pos (*.corec (*.state (e₁ +ₗ one) y-1 e₂)))
              e₃)
          p
          ( cong (_+ₗ y-1) q ∙
            sym (+ₗ-suc (ℕ.suc k ℕ.* (m ℕ.+ 0 ℕ.+ 1) ℕ.+ m) y-1))
          ( cong₂ {C = λ _ _ → Conat}
              (λ e₁ e₂ →
                pos (*.corec (*.state (e₁ +ₗ y-1) (e₂ +ₗ one) (e₂ +ₗ one))))
              r
              p ∙
            cong (λ e → *.corec′ (*.step′₂ (e .pred) (m ℕ.+ 0 +ₗ one)))
              (sym (+ₗ-suc (ℕ.suc k ℕ.* (m ℕ.+ 0) ℕ.+ m) y-1))))
        (cont (state (ℕ.suc k) ℕ.zero m y-1))
      where
      p : m ≡ m ℕ.+ 0
      p = solveℕ!
      q :
        ℕ.suc (ℕ.suc k) ℕ.* (m ℕ.+ 1) ℕ.+ 0 ≡
        ℕ.suc (ℕ.suc k ℕ.* (m ℕ.+ 0 ℕ.+ 1) ℕ.+ m)
      q = solveℕ!
      r : ℕ.suc (ℕ.suc k) ℕ.* m ℕ.+ 0 ≡ ℕ.suc k ℕ.* (m ℕ.+ 0) ℕ.+ m
      r = solveℕ!
    step′ k m (ℕ.suc n) zero =
      subst2
        (λ e₁ e₂ → StepR State e₁ (pos e₂))
        ( cong pos
            (sym
              (*.corec-fromℕ₊
                (m ℕ.+ n)
                (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m)
                (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m))) ∙
          cong
            (λ e →
              *.corec′
                (*.step′₂
                  ((e +ₗ one) .pred)
                  (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m +ₗ one)))
            p)
        (sym
          (*.corec-fromℕ₊ (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n) ℕ.+ m) n (m ℕ.+ ℕ.suc n)))
        (pos (cong (_+ₗ one) q))
      where
      p : ℕ.suc (m ℕ.+ n) ≡ m ℕ.+ ℕ.suc n
      p = solveℕ!
      q :
        ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m
          ℕ.+ (m ℕ.+ n) ℕ.* ℕ.suc (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n ℕ.+ 1) ℕ.+ m) ≡
        n ℕ.+ (ℕ.suc k ℕ.* (m ℕ.+ ℕ.suc n) ℕ.+ m) ℕ.* ℕ.suc (m ℕ.+ ℕ.suc n)
      q = solveℕ!
    step′ k (ℕ.suc m) ℕ.zero zero =
      pos
        ( *.corec-fromℕ₊
            (m ℕ.+ 0)
            (ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ 0 ℕ.+ 1) ℕ.+ ℕ.suc m)
            (ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ 0 ℕ.+ 1) ℕ.+ ℕ.suc m) ∙
          cong (_+ₗ one) p ∙
          sym
            (*.corec-fromℕ₊
              (m ℕ.+ 0 ℕ.+ k ℕ.* (ℕ.suc m ℕ.+ 0) ℕ.+ ℕ.suc m)
              (ℕ.suc m ℕ.+ 0)
              (ℕ.suc m ℕ.+ 0)))
      where
      p :
        ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ 0 ℕ.+ 1) ℕ.+ ℕ.suc m
          ℕ.+
            (m ℕ.+ 0)
              ℕ.* (ℕ.suc (ℕ.suc k ℕ.* (ℕ.suc m ℕ.+ 0 ℕ.+ 1) ℕ.+ ℕ.suc m)) ≡
        ℕ.suc m ℕ.+ 0
          ℕ.+
            (m ℕ.+ 0 ℕ.+ k ℕ.* (ℕ.suc m ℕ.+ 0) ℕ.+ ℕ.suc m)
              ℕ.* (ℕ.suc (ℕ.suc m ℕ.+ 0))
      p = solveℕ!
    step′ k ℕ.zero ℕ.zero zero =
      subst
        (λ e → StepR State zero (*.corec′ (*.step′₂ ((e +ₗ one) .pred) one)))
        p
        zero
      where
      p : 0 ≡ k ℕ.* 0 ℕ.+ 0
      p = solveℕ!

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state k m n y) = step′ k m n (predView y)

    open Bisim State step public

  module *-comm₁ where
    data State : Conat₊ → Conat₊ → Type where
      {-
                        n+x times
      /'''''''''''''''''''''''''''''''''''''''''''''
              y       n+y         n+y
           /'''''\/''''''''''\/''''''''''\/'''''''''
      ----->-----#-----------#-----------#-------...
      ----->---#---------#---------#---------#---...
      \___/\___/\________/\________/\________/\_____
        n    x     n+x       n+x       n+x
      \_____________________________________________
                        n+y times
      -}
      state :
        ∀ n x y →
        State
          (*.corec (*.state (n +ₗ x) y (n +ₗ y)))
          (*.corec (*.state (n +ₗ y) x (n +ₗ x)))

    step′ :
      ∀ n {x x-1 y y-1} → PredView x x-1 → PredView y y-1 →
      StepR State
        (*.corec′ (*.step′₁ (n +ₗ x) (y .pred) (n +ₗ y)))
        (*.corec′ (*.step′₁ (n +ₗ y) (x .pred) (n +ₗ x)))
    step′ n (pos x-1) (pos y-1) =
      cont
        (subst2
          (λ e₁ e₂ →
            State (*.corec (*.state e₁ y-1 e₂)) (*.corec (*.state e₂ x-1 e₁)))
          (sym (+ₗ-suc n x-1))
          (sym (+ₗ-suc n y-1))
          (state (ℕ.suc n) x-1 y-1))
    step′ n zero (pos y-1) =
      subst2
        (λ e₁ e₂ → StepR State (pos (*.corec (*.state (n +ₗ one) y-1 e₁))) e₂)
        (cong (_+ₗ y-1) p ∙ sym (+ₗ-suc n y-1))
        ( congS (λ e → pos (*.corec (*.state (e +ₗ y-1) (n +ₗ one) (n +ₗ one))))
            q ∙
          cong (λ e → *.corec′ (*.step′₂ (e .pred) (n +ₗ one)))
            (sym (+ₗ-suc n y-1)))
        (pos (*-comm₂.bisim (*-comm₂.state ℕ.zero ℕ.zero n y-1)))
      where
      p : n ℕ.+ 1 ℕ.+ 0 ℕ.+ 0 ≡ ℕ.suc n
      p = solveℕ!
      q : n ℕ.+ 0 ℕ.+ 0 ≡ n
      q = solveℕ!
    step′ n (pos x-1) zero =
      subst2
        (λ e₁ e₂ → StepR State e₁ (pos (*.corec (*.state (n +ₗ one) x-1 e₂))))
        ( congS (λ e → pos (*.corec (*.state (e +ₗ x-1) (n +ₗ one) (n +ₗ one))))
            q ∙
          cong (λ e → *.corec′ (*.step′₂ (e .pred) (n +ₗ one)))
            (sym (+ₗ-suc n x-1)))
        (cong (_+ₗ x-1) p ∙ sym (+ₗ-suc n x-1))
        (pos (sym (*-comm₂.bisim (*-comm₂.state ℕ.zero ℕ.zero n x-1))))
      where
      p : n ℕ.+ 1 ℕ.+ 0 ℕ.+ 0 ≡ ℕ.suc n
      p = solveℕ!
      q : n ℕ.+ 0 ℕ.+ 0 ≡ n
      q = solveℕ!
    step′ (ℕ.suc n) zero zero = pos refl
    step′ ℕ.zero zero zero = zero

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state n x y) = step′ n (predView x) (predView y)

    open Bisim State step public

  *-comm : ∀ x y → x * y ≡ y * x
  *-comm x y = *-comm₁.bisim (*-comm₁.state ℕ.zero x y)

  module *-distₗ-+ where
    data State : Conat₊ → Conat₊ → Type where
      state :
        ∀ x y₀ z z₀ →
        State
          (*.corec (*.state (+.corec (+.state x y₀)) z z₀))
          (+.corec (+.state (*.corec (*.state x z z₀)) (y₀ * z₀)))

    step′₂ :
      ∀ x-1 y₀ z₀ →
      StepR State
        (*.corec′ (*.step′₂ (+.corec′ (+.step′ x-1 y₀)) z₀))
        (+.corec′ (+.step′ (*.corec′ (*.step′₂ x-1 z₀)) (y₀ * z₀)))
    step′₂ (pos x-1) y₀ z₀ = cont (state x-1 y₀ z₀ z₀)
    step′₂ zero y₀ z₀ = pos refl

    step′₁ :
      ∀ x y₀ z-1 z₀ →
      StepR State
        (*.corec′ (*.step′₁ (+.corec (+.state x y₀)) z-1 z₀))
        (+.corec′ (+.step′ (*.corec′ (*.step′₁ x z-1 z₀)) (y₀ * z₀)))
    step′₁ x y₀ (pos z-1) z₀ = cont (state x y₀ z-1 z₀)
    step′₁ x y₀ zero z₀ = step′₂ (x .pred) y₀ z₀

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x y₀ z z₀) = step′₁ x y₀ (z .pred) z₀

    open Bisim State step public

  *-distₗ-+ : ∀ x y z → (x + y) * z ≡ x * z + y * z
  *-distₗ-+ x y z = *-distₗ-+.bisim (*-distₗ-+.state x y z z)

  module *-annihᵣ where
    data State : Conat₊ → Conat₊ → Type where
      state :
        ∀ x →
        State
          (*.corec (*.state x (inf.corec inf.state) inf))
          (inf.corec inf.state)

    step : ∀ {x y} → State x y → StepR State (x .pred) (y .pred)
    step (state x) = cont (state x)

    open Bisim State step public

  *-annihᵣ : ∀ x → x * inf ≡ inf
  *-annihᵣ x = *-annihᵣ.bisim (*-annihᵣ.state x)

  ------------------------------------------------------------------------------
  -- Exponentiation

  data Colist (A : Type) : Type
  record Colist₊ (A : Type) : Type

  data Colist A where
    none : Colist A
    some : Colist₊ A → Colist A

  record Colist₊ A where
    coinductive
    constructor untail
    field
      head : A
      tail : Colist A

  open Colist₊ public

  replicate : ∀ {A} → Conat₊ → A → Colist₊ A
  replicate′ : ∀ {A} → Conat → A → Colist A

  replicate x a .head = a
  replicate x a .tail = replicate′ (x .pred) a

  replicate′ zero a = none
  replicate′ (pos x-1) a = some (replicate x-1 a)

  module ^ where
    {- 4^3
    1:  state 0 [4, 4, 4] 4
    2:  state 1 [3, 4, 4] 4
    3:  state 1 [2, 4, 4] 4
    4:  state 1 [1, 4, 4] 4
    5:  state 2 [4, 3, 4] 4
    6:  state 2 [3, 3, 4] 4
    7:  state 2 [2, 3, 4] 4
    8:  state 2 [1, 3, 4] 4
    9:  state 2 [4, 2, 4] 4
    10: state 2 [3, 2, 4] 4
    ...
    15: state 2 [2, 1, 4] 4
    16: state 2 [1, 1, 4] 4
    17: state 3 [4, 4, 3] 4
    18: state 3 [3, 4, 3] 4
    ...
    33: state 3 [2, 1, 3] 4
    32: state 3 [1, 1, 3] 4
    33: state 3 [4, 4, 2] 4
    34: state 3 [3, 4, 2] 4
    ...
    63: state 3 [2, 1, 1] 4
    64: state 3 [1, 1, 1] 4
    -}
    data State : Type where
      state : ℕ → Colist₊ Conat₊ → Conat₊ → State

    reset : Step State → Step State
    reset zero = zero
    reset (pos x) = pos x
    reset (cont (state n xs x₀)) =
      cont (state (ℕ.suc n) (untail x₀ (some xs)) x₀)

    step′ : ℕ → Conat → Colist Conat₊ → Conat₊ → Step State
    step′ (ℕ.suc n) (pos x-1) xs x₀ = cont (state (ℕ.suc n) (untail x-1 xs) x₀)
    step′ (ℕ.suc n) zero (some xs) x₀ =
      reset (step′ n (xs .head .pred) (xs .tail) x₀)
    step′ (ℕ.suc n) zero none x₀ = zero
    step′ ℕ.zero (pos x-1) xs x₀ =
      cont (state (ℕ.suc ℕ.zero) (untail x-1 xs) x₀)
    step′ ℕ.zero zero xs x₀ = zero

    step : State → Step State
    step (state n xs x₀) = step′ n (xs .head .pred) (xs .tail) x₀

    open Corec State step public

  infixr 8 _^_
  _^_ : Conat₊ → Conat₊ → Conat₊
  x ^ y = ^.corec (^.state ℕ.zero (replicate y x) x)

  -- TODO: properties of exponentiation

--------------------------------------------------------------------------------
-- Operation on Conats

suc : Conat → Conat
suc x = pos (unpred x)

fromℕ : ℕ → Conat
fromℕ ℕ.zero = zero
fromℕ (ℕ.suc n) = pos (P.fromℕ₊ n)

fromℕ-inj : ∀ {x y} → fromℕ x ≡ fromℕ y → x ≡ y
fromℕ-inj {ℕ.zero} {ℕ.zero} p = refl
fromℕ-inj {ℕ.zero} {ℕ.suc y} p = ⊥.rec (zero≢pos p)
fromℕ-inj {ℕ.suc x} {ℕ.zero} p = ⊥.rec (zero≢pos (sym p))
fromℕ-inj {ℕ.suc x} {ℕ.suc y} p = cong ℕ.suc (P.fromℕ₊-inj (pos-inj p))

inf : Conat
inf = pos P.inf

inf≢fromℕ : ∀ n → inf ≡ fromℕ n → ⊥
inf≢fromℕ ℕ.zero p = zero≢pos (sym p)
inf≢fromℕ (ℕ.suc n) p = P.inf≢fromℕ₊ n (pos-inj p)

one : Conat
one = suc zero

infixl 6 _+_
_+_ : Conat → Conat → Conat
zero + y = y
pos x + zero = pos x
pos x + pos y = pos (x P.+ y)

+-fromℕ : ∀ x y → fromℕ x + fromℕ y ≡ fromℕ (x ℕ.+ y)
+-fromℕ ℕ.zero y = refl
+-fromℕ (ℕ.suc x) ℕ.zero = cong (λ e → pos (P.fromℕ₊ e)) p
  where
  p : x ≡ x ℕ.+ 0
  p = solveℕ!
+-fromℕ (ℕ.suc x) (ℕ.suc y) = cong pos (P.+-fromℕ₊ x y)

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl
+-assoc (pos x) zero z = refl
+-assoc (pos x) (pos y) zero = refl
+-assoc (pos x) (pos y) (pos z) = cong pos (P.+-assoc x y z)

+-idₗ : ∀ x → zero + x ≡ x
+-idₗ x = refl

+-comm : ∀ x y → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (pos y) = refl
+-comm (pos x) zero = refl
+-comm (pos x) (pos y) = cong pos (P.+-comm x y)

+-annihₗ : ∀ x → inf + x ≡ inf
+-annihₗ zero = refl
+-annihₗ (pos x) = cong pos (P.+-annihₗ x)

+-sucₗ : ∀ x y → suc x + y ≡ suc (x + y)
+-sucₗ zero zero = refl
+-sucₗ zero (pos y) = cong pos (P.+-oneₗ y)
+-sucₗ (pos x) zero = refl
+-sucₗ (pos x) (pos y) = cong pos (P.+-sucₗ x y)

infixl 7 _*_
_*_ : Conat → Conat → Conat
zero * y = zero
pos x * zero = zero
pos x * pos y = pos (x P.* y)

*-fromℕ : ∀ x y → fromℕ x * fromℕ y ≡ fromℕ (x ℕ.* y)
*-fromℕ ℕ.zero y = refl
*-fromℕ (ℕ.suc x) ℕ.zero = cong fromℕ p
  where
  p : 0 ≡ x ℕ.* 0
  p = solveℕ!
*-fromℕ (ℕ.suc x) (ℕ.suc y) = cong pos (P.*-fromℕ₊ x y)

*-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
*-assoc zero y z = refl
*-assoc (pos x) zero z = refl
*-assoc (pos x) (pos y) zero = refl
*-assoc (pos x) (pos y) (pos z) = cong pos (P.*-assoc x y z)

*-comm : ∀ x y → x * y ≡ y * x
*-comm zero zero = refl
*-comm zero (pos y) = refl
*-comm (pos x) zero = refl
*-comm (pos x) (pos y) = cong pos (P.*-comm x y)

*-idₗ : ∀ x → one * x ≡ x
*-idₗ zero = refl
*-idₗ (pos x) = cong pos (P.*-idₗ x)

*-annihₗ : ∀ x → zero * x ≡ zero
*-annihₗ x = refl

*-distₗ-+ : ∀ x y z → (x + y) * z ≡ x * z + y * z
*-distₗ-+ zero y z = refl
*-distₗ-+ (pos x) zero zero = refl
*-distₗ-+ (pos x) zero (pos z) = refl
*-distₗ-+ (pos x) (pos y) zero = refl
*-distₗ-+ (pos x) (pos y) (pos z) = cong pos (P.*-distₗ-+ x y z)

*-infᵣ : ∀ x → suc x * inf ≡ inf
*-infᵣ x = cong pos (P.*-annihᵣ (unpred x))

infixr 8 _^_
_^_ : Conat → Conat → Conat
x ^ zero = one
zero ^ pos y = zero
pos x ^ pos y = pos (x P.^ y)

-- from the Cubical Agda Library
separatedConat : Separated Conat
separatedConat₊ : Separated Conat₊

separatedConat zero zero f = refl
separatedConat zero (pos x) f = ⊥.rec (f λ p → zero≢pos p)
separatedConat (pos x) zero f = ⊥.rec (f λ p → zero≢pos (sym p))
separatedConat (pos x) (pos y) f =
  cong pos (separatedConat₊ x y λ g → f λ p → g (pos-inj p))

separatedConat₊ x y f i .pred =
  separatedConat (x .pred) (y .pred) (λ g → f λ p → g (cong pred p)) i

isSetConat : isSet Conat
isSetConat = Separated→isSet separatedConat

isSetConat₊ : isSet Conat₊
isSetConat₊ = Separated→isSet separatedConat₊ 
