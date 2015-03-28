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

module CoquandDybjer-STLC-sem where

open import Algebra using (module Monoid)

open import Data.List as List
  using (List; []; _∷_; _++_)
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

open import CoquandDybjer-STLC-norm

--
-- Convertibility.
--

infix 4 _≈_ _≃_

-- σ₁ ≃ σ₂

data _≃_ : ∀ {Γ Δ} (σ₁ σ₂ : Sub Γ Δ) → Set where
  ≃refl  : ∀ {Γ Δ} {σ : Sub Γ Δ} →
             σ ≃ σ
  ≃sym   : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} →
             σ₁ ≃ σ₂ → σ₂ ≃ σ₁
  ≃trans : ∀ {Γ Δ} {σ₁ σ₂ σ₃ : Sub Γ Δ} →
             σ₁ ≃ σ₂ → σ₂ ≃ σ₃ → σ₁ ≃ σ₃
  ≃assoc : ∀ {Γ Δ Δ′ Σ} {σ₁ : Sub Δ Γ} {σ₂ : Sub Δ′ Δ} {σ₃ : Sub Σ Δ′} →
             (σ₁ ⊙ σ₂) ⊙ σ₃ ≃ σ₁ ⊙ (σ₂ ⊙ σ₃)
  ≃idl   : ∀ {Γ Δ} {σ : Sub Γ Δ} →
             ı ⊙ σ ≃ σ
  ≃idr   : ∀ {Γ Δ} {σ : Sub Γ Δ} →
             σ ⊙ ı ≃ σ
  ≃wk    : ∀ {α Γ Δ} {σ : Sub Γ Δ} {t : Tm Γ α} →
             ↑ ⊙ (t ∷ σ) ≃ σ
  ≃cons  : ∀ {α Γ Δ Σ} {σ : Sub Δ Γ} {t : Tm Δ α} {σ′ : Sub Σ Δ} →
             (t ∷ σ) ⊙ σ′ ≃ (t [ σ′ ]) ∷ (σ ⊙ σ′)
  ≃id∷   : ∀ {α Γ} →
             ı {α ∷ Γ} ≃ ø ∷ (ı ⊙ ↑)

-- t₁ ≈ t₂

data _≈_  : ∀ {α Γ} (t₁ t₂ : Tm Γ α) → Set where
  ≈refl  : ∀ {α Γ} {t : Tm Γ α} →
             t ≈ t
  ≈sym   : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
             t₁ ≈ t₂ → t₂ ≈ t₁
  ≈trans : ∀ {α Γ} {t₁ t₂ t₃ : Tm Γ α} →
             t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
  ≈∙-cong  : ∀ {α β Γ} {t₁ t₂ : Tm Γ (α ⇒ β)} {u₁ u₂ : Tm Γ α} →
               t₁ ≈ t₂ → u₁ ≈ u₂ → t₁ ∙ u₁ ≈ t₂ ∙ u₂
  ≈[]-cong : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α } {σ₁ σ₂ : Sub Γ Δ} →
               t₁ ≈ t₂ → σ₁ ≃ σ₂ → t₁ [ σ₁ ] ≈ t₂ [ σ₂ ]
  ≈λ-cong  : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
               t₁ ≈ t₂ → (ƛ t₁) ≈ (ƛ t₂)
  ≈proj  : ∀ {α Γ Δ} {t : Tm Γ α } {σ : Sub Γ Δ} →
             ø [ t ∷ σ ] ≈ t
  ≈id    : ∀ {α Γ} {t : Tm Γ α} →
             t [ ı ] ≈ t
  ≈comp  : ∀ {α Γ Δ Σ} {t : Tm Δ α} {σ : Sub Γ Δ} {σ′ : Sub Σ Γ} →
             t [ σ ⊙ σ′ ] ≈ t [ σ ] [ σ′ ]
  ≈lam   : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} →
             (ƛ t) [ σ ] ≈ (ƛ t [ ø ∷ (σ ⊙ ↑) ])
  ≈app   : ∀ {α β Γ Δ} {t₁ : Tm Δ (α ⇒ β)} {t₂ : Tm Δ α} {σ : Sub Γ Δ} →
             (t₁ ∙ t₂) [ σ ] ≈ t₁ [ σ ] ∙ (t₂ [ σ ])

-- ≃-Reasoning

≃setoid : {Γ Δ : Ctx} → Setoid _ _

≃setoid {Γ} {Δ} = record
  { Carrier = Sub Γ Δ
  ; _≈_ = _≃_
  ; isEquivalence = record
    { refl = ≃refl
    ; sym = ≃sym
    ; trans = ≃trans } }

module ≃-Reasoning {Γ} {Δ} = EqReasoning (≃setoid {Γ} {Δ})

-- ≈-Reasoning

≈setoid : {Γ : Ctx} {α : Ty} → Setoid _ _

≈setoid {Γ} {α} = record
  { Carrier = Tm Γ α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {Γ} {α : Ty} = EqReasoning (≈setoid {Γ} {α})
