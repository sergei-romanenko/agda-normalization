{-
  Normalization theorem for the Simply Typed Lambda-Calculus:

    "every typable term is normalizable".

  Based on

    Thierry Coquand and Peter Dybjer. 1997.
    Intuitionistic model constructions and normalization proofs.
    Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
    DOI=10.1017/S0960129596002150 http://dx.doi.org/10.1017/S0960129596002150 

  and

    Thorsten Altenkirch and James Chapman. 2009.
    Big-step normalisation.
    J. Funct. Program. 19, 3-4 (July 2009), 311-333.
    DOI=10.1017/S0956796809007278 http://dx.doi.org/10.1017/S0956796809007278 

-}

{-# OPTIONS --no-positivity-check #-}

module CoquandDybjer-STLC-norm where

open import Data.List
  hiding ([_])
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
--open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

open Membership-≡

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

Ctx : Set
Ctx = List Ty

mutual

  infixl 5 _∙_ _[_]
  infixr 3 ƛ_

  -- Terms.

  data Tm : Ctx → Ty → Set where
    ø   : ∀ {α Γ} → Tm (α ∷ Γ) α
    _∙_ : ∀ {α β Γ} (t : Tm Γ (α ⇒ β)) (t′ : Tm Γ α) → Tm Γ β
    ƛ_  : ∀ {α β Γ} (t : Tm (α ∷ Γ) β) → Tm Γ (α ⇒ β)
    _[_] : ∀ {α Γ Δ} (t : Tm Δ α) (σ : Sub Γ Δ) → Tm Γ α

  -- Substitutions: `Sub Γ Δ` transforms `Tm Δ α` into `Tm Γ α`.

  data Sub : (Γ Δ : Ctx) → Set where
    ı   : ∀ {Γ} → Sub Γ Γ
    _⊙_ : ∀ {Γ Δ Σ} (σ : Sub Γ Δ) (σ′ : Sub Σ Γ) → Sub Σ Δ
    _∷_ : ∀ {α Γ Δ} (t : Tm Γ α) (σ : Sub Γ Δ) → Sub Γ (α ∷ Δ)
    ↑  : ∀ {α Γ} → Sub (α ∷ Γ) Γ


--
-- Example terms.
--

I : ∀ {α} → Tm [] (α ⇒ α)
I {α} = ƛ ø

--K = λ x y → x
K : ∀ {α β} → Tm [] (α ⇒ β ⇒ α)
K = ƛ ƛ ø [ ↑ ]

--S = λ x y z → (x ∙ z) ∙ (y ∙ z)
S : ∀ {α β γ} → Tm [] ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
S = ƛ ƛ ƛ (ø [ ↑ ] [ ↑ ] ∙ ø) ∙ (ø [ ↑ ] ∙ ø)

SKK : ∀ {α} → Tm [] (α ⇒ α)
SKK {α} = S {α} ∙ K {α} ∙ K {α} {α}

K-SKK : ∀ α β → Tm [] (α ⇒ β ⇒ β)
K-SKK α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm [] (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})


--
-- Weak head normal forms.
--

data Var : Ctx → Ty → Set where
  vz : ∀ {α Γ} → Var (α ∷ Γ) α
  vs : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

data Ne (T : Ctx → Ty → Set) : Ctx → Ty → Set where
  var : ∀ {α Γ} (x : Var Γ α) → Ne T Γ α
  app : ∀ {α β Γ} (f : Ne T Γ (α ⇒ β)) (u : T Γ α) → Ne T Γ β


module NaiveNorm where
  mutual

    data Val : Ctx → Ty → Set where
      ne  : ∀ {α Γ} (n : Ne Val Γ α) → Val Γ α
      lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → Val Γ (α ⇒ β)

    data Env (Γ : Ctx) : Ctx → Set where
      []  : Env Γ []
      _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)

  {-# TERMINATING #-}
  mutual

    infixl 5 _⟨∙⟩_

    ⟦_⟧_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) → Val Γ α
    ⟦ ø ⟧ (u ∷ ρ) = u
    ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
    ⟦ ƛ t ⟧ ρ = lam t ρ
    ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

    ⟦_⟧*_ : ∀ {Γ Δ Σ} (σ : Sub Γ Δ) (ρ : Env Σ Γ) → Env Σ Δ
    ⟦ ı ⟧* ρ = ρ
    ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
    ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
    ⟦ ↑ ⟧* (u ∷ ρ) = ρ

    _⟨∙⟩_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) → Val Γ β
    ne n ⟨∙⟩ v = ne (app n v)
    lam t ρ ⟨∙⟩ v = ⟦ t ⟧ (v ∷ ρ)

    ⟦III⟧ : ⟦ III ⟧ ([] {[]}) ≡ lam ø []
    ⟦III⟧ = refl

    ⟦SKK⟧ : ⟦ SKK {⋆} ⟧ ([] {[]}) ≡
      lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
          (lam (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))
    ⟦SKK⟧ = refl

    ⟦SKK∙I⟧ : ⟦ SKK ∙ I {⋆} ⟧ ([] {[]}) ≡ lam ø []
    ⟦SKK∙I⟧ = refl


--
-- A "denotational" semantics for `Tm α`.
--

module DenotationalNorm where

  D : (α : Ty) → Set
  D ⋆ = ⊥
  D (α ⇒ β) = D α → D β

  data DEnv (Γ : Ctx) : Ctx → Set where
    []  : DEnv Γ []
    _∷_ : ∀ {α Δ} (u : D α) (ρ : DEnv Γ Δ) → DEnv Γ (α ∷ Δ)


  mutual

    ⟦_⟧_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : DEnv Γ Δ) → D α
    ⟦ ø ⟧ (u ∷ ρ) = u
    ⟦ t ∙ t′ ⟧ ρ = (⟦ t ⟧ ρ) (⟦ t′ ⟧ ρ)
    ⟦ ƛ t ⟧ ρ = λ u → ⟦ t ⟧ (u ∷ ρ)
    ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

    ⟦_⟧*_ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : DEnv Γ Δ) → DEnv Γ Σ
    ⟦ ı ⟧* ρ = ρ
    ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
    ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
    ⟦ ↑ ⟧* (u ∷ ρ) = ρ

    ⟦III⟧ : ⟦ III ⟧ ([] {[]}) ≡ (λ u → u)
    ⟦III⟧ = refl

    ⟦SKK⟧ : ⟦ SKK {⋆} ⟧ ([] {[]}) ≡ (λ u → u)
    ⟦SKK⟧ = refl

  -- The problem is how to "reify" D-values?
  -- (= How to go back to first-order terms?)
  -- (How compare functions for equality?)

--
-- Gluing
--

mutual

  data GVal : Ctx → Ty → Set where
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : GEnv Γ Δ) → GVal Γ (α ⇒ β)
    ne  : ∀ {α Γ} → Ne GVal Γ α → GVal Γ α

  {-
  data GEnv (Γ : Ctx) : Ctx → Set where
    []  : ∀ {Γ} → GEnv Γ []
    _∷_ : ∀ {α Δ Γ} (u : G Γ α) (ρ : GEnv Γ Δ) → GEnv Γ (α ∷ Δ)
  -}
  GEnv : (Γ Δ : Ctx) → Set
  GEnv Γ [] = ⊤
  GEnv Γ (α ∷ Δ) = G Γ α × GEnv Γ Δ

  G : (Γ : Ctx) (α : Ty) → Set
  G Γ ⋆ = GVal Γ ⋆
  G Γ (α ⇒ β) = GVal Γ (α ⇒ β) × (G Γ α → G Γ β)

-- ⌈_⌉

⌈_⌉ : ∀ {α Γ} (p : G Γ α) → GVal Γ α
⌈_⌉ {⋆} u = u
⌈_⌉ {α ⇒ β} p = proj₁ p


{-
-- ⟪_⟫

⟪_⟫ : ∀ {Γ α} (p : G Γ α) → Tm Γ α
⟪_⟫ {Γ} {⋆} ()
⟪_⟫ {Γ} {α ⇒ β} p = proj₁ p
-}

-- Application for glued values.

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {Γ α β} (p : G Γ (α ⇒ β)) (q : G Γ α) → G Γ β
p ⟨∙⟩ q = proj₂ p q

-- Glued semantics terminates!
-- (Note that the positivity check has been turned off! :-( )

mutual

  ⟦_⟧_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : GEnv Γ Δ) → G Γ α
  ⟦ ø ⟧ (u , ρ) = u
  ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
  ⟦ ƛ t ⟧ ρ = lam t ρ , λ g → ⟦ t ⟧ (g , ρ)
  ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

  ⟦_⟧*_ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : GEnv Γ Δ) → GEnv Γ Σ
  ⟦ ı ⟧* ρ = ρ
  ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
  ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ , ⟦ σ ⟧* ρ
  ⟦ ↑ ⟧* (u , ρ) = ρ
