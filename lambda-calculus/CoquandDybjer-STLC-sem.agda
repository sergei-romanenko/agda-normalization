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
  ≈ƛ-cong  : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
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

--
-- Completeness: the normal forms of two convertible terms are equal
--     t₁ ≈ t₂ → norm t₁ ≡ norm t₂
--

postulate
  reify∘⟨∙⟩ : ∀ {α β Γ Δ} (t : Tm Δ (α ⇒ β)) (u : Tm Δ α) (ρ : VEnv Γ Δ) →
    ⟪ ⟦ t ⟧ ρ ⟨∙⟩ ⟦ u ⟧ ρ ⟫ ≡ ⟪ ⟦ t ⟧ ρ ⟫ ∙ ⟪ ⟦ u ⟧ ρ ⟫

postulate
  sound≃ : ∀ {Γ Δ Σ} {σ₁ σ₂ : Sub Δ Σ} {ρ : VEnv Γ Δ} →
    σ₁ ≃ σ₂ → ⟦ σ₁ ⟧* ρ ≡ ⟦ σ₂ ⟧* ρ

mutual

  wkVEnv∘⟦⟧* : ∀ {Γ Δ Δ′} Σ (σ : Sub Δ Δ′) (ρ : VEnv Γ Δ) →
    wkVEnv* Σ (⟦ σ ⟧* ρ) ≡ ⟦ σ ⟧* (wkVEnv* Σ ρ)
  wkVEnv∘⟦⟧* Σ ı ρ = refl
  wkVEnv∘⟦⟧* Σ (σ₁ ⊙ σ₂) ρ = begin
    wkVEnv* Σ (⟦ σ₁ ⟧* (⟦ σ₂ ⟧* ρ))
      ≡⟨ wkVEnv∘⟦⟧* Σ σ₁ (⟦ σ₂ ⟧* ρ) ⟩
    ⟦ σ₁ ⟧* (wkVEnv* Σ (⟦ σ₂ ⟧* ρ))
      ≡⟨ cong ⟦ σ₁ ⟧* (wkVEnv∘⟦⟧* Σ σ₂ ρ) ⟩
    ⟦ σ₁ ⟧* (⟦ σ₂ ⟧* (wkVEnv* Σ ρ))
    ∎
    where open ≡-Reasoning
  wkVEnv∘⟦⟧* Σ (t ∷ σ) ρ = begin
    wkVal* Σ (⟦ t ⟧ ρ) ∷ wkVEnv* Σ (⟦ σ ⟧* ρ)
      ≡⟨ cong₂ _∷_ (wkVal*∘⟦⟧ Σ t ρ) (wkVEnv∘⟦⟧* Σ σ ρ) ⟩
    (⟦ t ⟧ (wkVEnv* Σ ρ)) ∷ (⟦ σ ⟧* (wkVEnv* Σ ρ))
    ∎
    where open ≡-Reasoning
  wkVEnv∘⟦⟧* Σ ↑ (v ∷ ρ) = refl

  wkVal*∘⟦⟧ : ∀ {α Γ Δ} Σ (t : Tm Δ α) (ρ : VEnv Γ Δ) →
    wkVal* Σ (⟦ t ⟧ ρ) ≡ ⟦ t ⟧ (wkVEnv* Σ ρ)
  --wkVal*∘⟦⟧ Σ t ρ = {!!}
  wkVal*∘⟦⟧ Σ ø (v ∷ ρ) = refl
  wkVal*∘⟦⟧ {β} {Γ} Σ (t₁ ∙ t₂) ρ = begin
    wkVal* Σ (⟦ t₁ ⟧ ρ ⟨∙⟩ ⟦ t₂ ⟧ ρ)
      ≡⟨⟩
    wkVal* Σ (⟦ t₁ ⟧ ρ [] (⟦ t₂ ⟧ ρ))
      ≡⟨ wkVal*∘$ Σ (⟦ t₁ ⟧ ρ) (⟦ t₂ ⟧ ρ) ⟩
    ⟦ t₁ ⟧ ρ Σ (wkVal* Σ (⟦ t₂ ⟧ ρ))
      ≡⟨⟩
    wkVal* Σ (⟦ t₁ ⟧ ρ) ⟨∙⟩ wkVal* Σ (⟦ t₂ ⟧ ρ)
      ≡⟨ cong₂ _⟨∙⟩_ (wkVal*∘⟦⟧ Σ t₁ ρ) (wkVal*∘⟦⟧ Σ t₂ ρ) ⟩
    ⟦ t₁ ⟧ (wkVEnv* Σ ρ) ⟨∙⟩ ⟦ t₂ ⟧ (wkVEnv* Σ ρ)
    ∎
    where open ≡-Reasoning
  wkVal*∘⟦⟧ Σ (ƛ t) ρ =
    wkVal* Σ (⟦ ƛ t ⟧ ρ) ≡ ⟦ ƛ t ⟧ (wkVEnv* Σ ρ) ∋
    {!!}
  wkVal*∘⟦⟧ Σ (t [ σ ]) ρ = begin
    wkVal* Σ (⟦ t ⟧ (⟦ σ ⟧* ρ))
      ≡⟨ wkVal*∘⟦⟧ Σ t (⟦ σ ⟧* ρ) ⟩
    ⟦ t ⟧ (wkVEnv* Σ (⟦ σ ⟧* ρ))
      ≡⟨ cong ⟦ t ⟧ (wkVEnv∘⟦⟧* Σ σ ρ) ⟩
    ⟦ t ⟧ (⟦ σ ⟧* (wkVEnv* Σ ρ))
    ∎
    where open ≡-Reasoning

  wkVal*∘$ : ∀ {α β Γ} Σ → (u₁ : Val Γ (α ⇒ β)) (u₂ : Val Γ α) →
    wkVal* {β} {Γ} Σ (u₁ [] u₂) ≡ u₁ Σ (wkVal* {α} {Γ} Σ u₂)
  wkVal*∘$ {α} {β} {Γ} Σ u₁ u₂ = {!!}

sound : ∀ {Γ Δ α} {t₁ t₂ : Tm Δ α} →
  t₁ ≈ t₂ → ∀ (ρ : VEnv Γ Δ) → ⟪ ⟦ t₁ ⟧ ρ ⟫ ≡ ⟪ ⟦ t₂ ⟧ ρ ⟫
sound ≈refl ρ =
  refl
sound (≈sym t₁≈t₂) ρ =
  sym (sound t₁≈t₂ ρ)
sound (≈trans t₁≈t₂ t₂≈t₃) ρ =
  trans (sound t₁≈t₂ ρ) (sound t₂≈t₃ ρ)
sound (≈∙-cong {α} {β} {Γ} {t₁} {t₂} {u₁} {u₂} t₁≈t₂ u₁≈u₂) ρ = begin
  ⟪ ⟦ t₁ ⟧ ρ ⟨∙⟩ ⟦ u₁ ⟧ ρ ⟫
    ≡⟨ reify∘⟨∙⟩ t₁ u₁ ρ ⟩
  ⟪ ⟦ t₁ ⟧ ρ ⟫ ∙ ⟪ ⟦ u₁ ⟧ ρ ⟫
    ≡⟨ cong₂ _∙_ (sound t₁≈t₂ ρ) (sound u₁≈u₂ ρ) ⟩
  ⟪ ⟦ t₂ ⟧ ρ ⟫ ∙ ⟪ ⟦ u₂ ⟧ ρ ⟫
    ≡⟨ sym $ reify∘⟨∙⟩ t₂ u₂ ρ ⟩
  ⟪ ⟦ t₂ ⟧ ρ ⟨∙⟩ ⟦ u₂ ⟧ ρ ⟫
  ∎
  where open ≡-Reasoning
sound (≈[]-cong {α} {Γ} {Δ} {t₁} {t₂} {σ₁} {σ₂} t₁≈t₂ σ₁≃σ₂) ρ = begin
    ⟪ ⟦ t₁ ⟧ (⟦ σ₁ ⟧* ρ) ⟫
      ≡⟨ cong (λ ρ′ → ⟪ ⟦ t₁ ⟧ ρ′ ⟫) (sound≃ σ₁≃σ₂) ⟩
    ⟪ ⟦ t₁ ⟧ (⟦ σ₂ ⟧* ρ) ⟫
      ≡⟨ sound t₁≈t₂ (⟦ σ₂ ⟧* ρ) ⟩
    ⟪ ⟦ t₂ ⟧ (⟦ σ₂ ⟧* ρ) ⟫
  ∎
  where open ≡-Reasoning
sound (≈ƛ-cong {α} {β} {Γ} {t₁} {t₂} t₁≈t₂) ρ =
  cong ƛ_ (sound t₁≈t₂ (reflect (var vz) ∷ wkVEnv ρ))
sound ≈proj ρ =
  refl
sound ≈id ρ =
  refl
sound ≈comp ρ =
  refl
sound (≈lam {α} {β} {Γ} {Δ} {t} {σ}) ρ =
  {-begin
    ƛ ⟪ ⟦ t ⟧ (reflect (var vz) ∷ wkVEnv (⟦ σ ⟧* ρ)) ⟫
      ≡⟨ cong (λ ρ′ → ƛ ⟪ ⟦ t ⟧ (reflect (var vz) ∷ ρ′) ⟫)
              (wkVEnv∘⟦⟧* (α ∷ []) σ ρ)  ⟩
    ƛ ⟪ ⟦ t ⟧ (reflect (var vz) ∷ ⟦ σ ⟧* (wkVEnv ρ)) ⟫
  ∎-}
  -- ƛ embNf (reify (⟦ t ⟧ (reflect (var vz) ∷ wkVEnv* (α ∷ []) (⟦ σ ⟧* ρ))))
  -- ƛ embNf (reify (⟦ t ⟧ (reflect (var vz) ∷ ⟦ σ ⟧* (wkVEnv* (α ∷ []) ρ))))
  {!!} {-begin
  {!!}
    ≡⟨ {!!} ⟩
  {!!}-}
  where open ≡-Reasoning
sound ≈app ρ =
  refl

norm′ : ∀ {α Γ} (t : Tm Γ α) (ρ : VEnv Γ Γ) → Tm Γ α
norm′ t ρ = ⟪ ⟦ t ⟧ ρ ⟫

norm-sound : ∀ {Γ α} {t₁ t₂ : Tm Γ α} →
  t₁ ≈ t₂ → norm t₁ ≡ norm t₂
norm-sound t₁≈t₂ =
  sound t₁≈t₂ idVEnv
