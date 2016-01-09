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

  and

    James Chapman. 2009. Type Checking and Normalization.
    Ph.D. thesis, School of Computer Science, University of Nottingham.
-}

module STLC-Tait-OPE where

open import Data.List as List
  hiding ([_])
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Properties
  using ()
open import Data.Empty
open import Data.Unit
  using (⊤; tt)
open import Data.Product

open import Function
--import Function.Related as Related

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

{-
open Membership-≡

open import Algebra
  using (module Monoid)
private
  module LM {a} {A : Set a} = Monoid (List.monoid A)
-}


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

  infixl 6 _[_]
  infixr 6 _⊙_
  infixr 5 _∷_
  infixl 5 _∙_
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
    _⊙_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ) (σ′ : Sub Γ′ Δ) → Sub Γ′ Γ
    _∷_ : ∀ {α Γ Δ} (t : Tm Γ α) (σ : Sub Γ Δ) → Sub Γ (α ∷ Δ)
    ↑  : ∀ {α Γ} → Sub (α ∷ Γ) Γ


--
-- Example terms.
--

-- I = λ x → x
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
-- A "denotational" semantics for `Tm α`.
--

module DenotationalEval where

  D : (α : Ty) → Set
  D ⋆ = ⊤
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

    ⟦_⟧*_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ′) (ρ : DEnv Γ Δ) → DEnv Γ Γ′
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
-- Convertibility.
--

infix 4 _≈_ _≃_

mutual

  -- σ₁ ≃ σ₂

  data _≃_ : ∀ {Γ Δ} (σ₁ σ₂ : Sub Γ Δ) → Set where
    ≃refl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ≃ σ
    ≃sym : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} →
      σ₁ ≃ σ₂ → σ₂ ≃ σ₁
    ≃trans : ∀ {Γ Δ} {σ₁ σ₂ σ₃ : Sub Γ Δ} →
      σ₁ ≃ σ₂ → σ₂ ≃ σ₃ → σ₁ ≃ σ₃
    ≃⊙-cong : ∀ {Γ Δ Γ′} {σ₁ σ₂ : Sub Δ Γ} {τ₁ τ₂ : Sub Γ′ Δ} →
      σ₁ ≃ σ₂ → τ₁ ≃ τ₂ → σ₁ ⊙ τ₁ ≃ σ₂ ⊙ τ₂
    ≃∷-cong : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α} {σ₁ σ₂ : Sub Δ Γ} →
      t₁ ≈ t₂ → σ₁ ≃ σ₂ → t₁ ∷ σ₁ ≃ t₂ ∷ σ₂
    ≃assoc : ∀ {Γ Δ Δ′ Γ′} {σ₁ : Sub Δ Γ} {σ₂ : Sub Δ′ Δ} {σ₃ : Sub Γ′ Δ′} →
      (σ₁ ⊙ σ₂) ⊙ σ₃ ≃ σ₁ ⊙ (σ₂ ⊙ σ₃)
    ≃idl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      ı ⊙ σ ≃ σ
    ≃idr : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ⊙ ı ≃ σ
    ≃wk : ∀ {α Γ Δ} {σ : Sub Γ Δ} {t : Tm Γ α} →
      ↑ ⊙ (t ∷ σ) ≃ σ
    ≃cons : ∀ {α Γ Δ Γ′} {σ : Sub Δ Γ} {t : Tm Δ α} {σ′ : Sub Γ′ Δ} →
      (t ∷ σ) ⊙ σ′ ≃ t [ σ′ ] ∷ (σ ⊙ σ′)
    ≃id∷ : ∀ {α Γ} →
      ı {α ∷ Γ} ≃ ø ∷ (ı ⊙ ↑)

  -- t₁ ≈ t₂

  data _≈_  : ∀ {α Γ} (t₁ t₂ : Tm Γ α) → Set where
    ≈refl : ∀ {α Γ} {t : Tm Γ α} →
      t ≈ t
    ≈sym : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₁
    ≈trans : ∀ {α Γ} {t₁ t₂ t₃ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
    ≈∙-cong : ∀ {α β Γ} {t₁ t₂ : Tm Γ (α ⇒ β)} {u₁ u₂ : Tm Γ α} →
      t₁ ≈ t₂ → u₁ ≈ u₂ → t₁ ∙ u₁ ≈ t₂ ∙ u₂
    ≈[]-cong : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α } {σ₁ σ₂ : Sub Γ Δ} →
      t₁ ≈ t₂ → σ₁ ≃ σ₂ → t₁ [ σ₁ ] ≈ t₂ [ σ₂ ]
    ≈ƛ-cong : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
      t₁ ≈ t₂ → (ƛ t₁) ≈ (ƛ t₂)
    ≈proj : ∀ {α Γ Δ} {t : Tm Γ α } {σ : Sub Γ Δ} →
      ø [ t ∷ σ ] ≈ t
    ≈id : ∀ {α Γ} {t : Tm Γ α} →
      t [ ı ] ≈ t
    ≈comp : ∀ {α Γ Δ Γ′} {t : Tm Δ α} {σ : Sub Γ Δ} {σ′ : Sub Γ′ Γ} →
      t [ σ ⊙ σ′ ] ≈ t [ σ ] [ σ′ ]
    ≈lam : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} →
      (ƛ t) [ σ ] ≈ (ƛ t [ ø ∷ (σ ⊙ ↑) ])
    ≈app : ∀ {α β Γ Δ} {t₁ : Tm Δ (α ⇒ β)} {t₂ : Tm Δ α} {σ : Sub Γ Δ} →
      (t₁ ∙ t₂) [ σ ] ≈ t₁ [ σ ] ∙ t₂ [ σ ]
    ≈βσ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) (α ⇒ β)} {σ : Sub Γ Δ} {t′ : Tm Γ α} →
               (ƛ t) [ σ ] ∙ t′ ≈ t [ t′ ∷ σ ]
    ≈η : ∀ {α β Γ} {t : Tm Γ (α ⇒ β)} →
      t ≈ (ƛ (t [ ↑ ] ∙ ø))

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
-- Weak head normal forms.
--

data Var : Ctx → Ty → Set where
  vz : ∀ {α Γ} → Var (α ∷ Γ) α
  vs : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

data Ne (T : Ctx → Ty → Set) : Ctx → Ty → Set where
  var : ∀ {α Γ} (x : Var Γ α) → Ne T Γ α
  app : ∀ {α β Γ} (f : Ne T Γ (α ⇒ β)) (u : T Γ α) → Ne T Γ β

mutual

  data Val : Ctx → Ty → Set where
    ne  : ∀ {α Γ} (us : Ne Val Γ α) → Val Γ α
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → Val Γ (α ⇒ β)

  data Env (Γ : Ctx) : Ctx → Set where
    []  : Env Γ []
    _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)


module NaiveEval where

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
    ne us ⟨∙⟩ u = ne (app us u)
    lam t ρ ⟨∙⟩ u = ⟦ t ⟧ (u ∷ ρ)

  ⟦III⟧ : ⟦ III ⟧ ([] {[]}) ≡ lam ø []
  ⟦III⟧ = refl

  ⟦SKK⟧ : ⟦ SKK {⋆} ⟧ ([] {[]}) ≡
    lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
        (lam (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))
  ⟦SKK⟧ = refl

  ⟦SKK∙I⟧ : ⟦ SKK ∙ I {⋆} ⟧ ([] {[]}) ≡ lam ø []
  ⟦SKK∙I⟧ = refl
  

--
-- η-long β-normal forms.
--

data Nf (Γ : Ctx) : Ty → Set where
  ne  : ∀ (ns : Ne Nf Γ ⋆) → Nf Γ ⋆
  lam : ∀ {α β} (n : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)


--
-- Embedding of values and normal forms into terms.
--

embVar : ∀ {α Γ} (x : Var Γ α) → Tm Γ α
embVar vz = ø
embVar (vs x) = embVar x [ ↑ ]

sub-from-[] : ∀ {Γ} → Sub Γ []
sub-from-[] {[]} = ı
sub-from-[] {α ∷ Γ} = sub-from-[] ⊙ ↑

mutual

  embNeVal : ∀ {α Γ} (us : Ne Val Γ α) → Tm Γ α
  embNeVal (var x) = embVar x
  embNeVal (app us u) = embNeVal us ∙ embVal u

  embVal : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  embVal (lam t ρ) =
    ƛ t [ ø ∷ (embEnv ρ ⊙ ↑) ]
  embVal (ne us) = embNeVal us

  embEnv : ∀ {Γ Δ} (ρ : Env Γ Δ) → Sub Γ Δ
  embEnv [] = sub-from-[]
  embEnv (u ∷ ρ) = embVal u ∷ embEnv ρ

mutual

  embNeNf : ∀ {α Γ} (ns : Ne Nf Γ α) → Tm Γ α
  embNeNf (var x) = embVar x
  embNeNf (app ns n) = embNeNf ns ∙ embNf n

  embNf : ∀ {α Γ} (n : Nf Γ α) → Tm Γ α
  embNf (lam n) = ƛ embNf n
  embNf (ne ns) = embNeNf ns


--
-- Weakening contexts by means of order preserving embeddings.
--

infix 4 _≤_

data _≤_ : (Γ Δ : Ctx) → Set where
  ≤id : ∀{Γ} → Γ ≤ Γ
  ≤weak : ∀{Γ Δ α} → Γ ≤ Δ → α ∷ Γ ≤ Δ
  ≤lift : ∀{Γ Δ α} → Γ ≤ Δ → α ∷ Γ ≤ α ∷ Δ

infixr 6 _●_

_●_ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (η′ : Γ ≤ Δ) → Β ≤ Δ
≤id ● η′ = η′
≤weak η ● η′ = ≤weak (η ● η′)
≤lift η ● ≤id = ≤lift η
≤lift η ● ≤weak η′ = ≤weak (η ● η′)
≤lift η ● ≤lift η′ = ≤lift (η ● η′)

η●≤id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η ● ≤id ≡ η
η●≤id ≤id = refl
η●≤id (≤weak η) = cong ≤weak (η●≤id η)
η●≤id (≤lift η) = refl

var≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (x : Var Δ α) → Var Γ α
var≤ ≤id x = x
var≤ (≤weak η) x = vs (var≤ η x)
var≤ (≤lift η) vz = vz
var≤ (≤lift η) (vs x) = vs (var≤ η x)

mutual

  val≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (u : Val Δ α) → Val Γ α
  val≤ η (ne us) = ne (neVal≤ η us)
  val≤ η (lam t ρ) = lam t (env≤ η ρ)

  neVal≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (us : Ne Val Δ α) → Ne Val Γ α
  neVal≤ η (var x) = var (var≤ η x)
  neVal≤ η (app us u) = app (neVal≤ η us) (val≤ η u)

  env≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ρ : Env Δ α) → Env Γ α
  env≤ η [] = []
  env≤ η (u ∷ ρ) = val≤ η u ∷ env≤ η ρ

  nf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (n : Nf Δ α) → Nf Γ α
  nf≤ η (ne ns) = ne (neNf≤ η ns)
  nf≤ η (lam n) = lam (nf≤ (≤lift η) n)

  neNf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ns : Ne Nf Δ α) → Ne Nf Γ α
  neNf≤ η (var x) = var (var≤ η x)
  neNf≤ η (app ns n) = app (neNf≤ η ns) (nf≤ η n)

--
-- Weakening
--

wk : ∀ {α Γ} → α ∷ Γ ≤ Γ
wk = ≤weak ≤id

wkNeVal : ∀ {α β Γ} (us : Ne Val Γ α) → Ne Val (β ∷ Γ) α
wkNeVal = neVal≤ wk

wkVal : ∀ {α β Γ} (u : Val Γ α) → Val (β ∷ Γ) α
wkVal = val≤ wk

wkEnv : ∀ {α Γ Δ} (ρ : Env Γ Δ) → Env (α ∷ Γ) Δ
wkEnv = env≤ wk

-- We can iterate weakenings using contexts.

wkNeVal* : ∀ {α} Δ {Γ} (us : Ne Val Γ α) → Ne Val (Δ ++ Γ) α
wkNeVal* [] us = us
wkNeVal* (α ∷ Δ) us = wkNeVal (wkNeVal* Δ us)

wkVal* : ∀ {α} Δ {Γ} (u : Val Γ α) → Val (Δ ++ Γ) α
wkVal* [] u = u
wkVal* (α ∷ Δ) u = wkVal (wkVal* Δ u)

wkEnv* : ∀ {Β} Δ {Γ} (ρ : Env Γ Β) → Env (Δ ++ Γ) Β
wkEnv* [] ρ = ρ
wkEnv* (α ∷ Δ) ρ = wkEnv (wkEnv* Δ ρ)

-- Identity environments.

id-env : ∀ {Γ} → Env Γ Γ
id-env {[]} = []
id-env {α ∷ Γ} = ne (var vz) ∷ wkEnv id-env


--
-- Recursive normalizer.
--

module NaiveNorm where

  open NaiveEval

  {-# TERMINATING #-}
  mutual

    qVal : ∀ {α Γ} (u : Val Γ α) → Nf Γ α
    qVal {⋆} (ne us) = ne (qNeVal us)
    qVal {α ⇒ β} f =
      lam (qVal (wkVal f ⟨∙⟩ ne (var vz)))

    qNeVal : ∀ {α Γ} (us : Ne Val Γ α) → Ne Nf Γ α
    qNeVal (var x) = var x
    qNeVal (app us u) = app (qNeVal us) (qVal u)

  nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
  nf t = qVal (⟦ t ⟧ id-env)

  nf-III : nf III ≡ lam (ne (var vz))
  nf-III = refl

  nf-SKK : nf (SKK {⋆}) ≡ lam (ne (var vz))
  nf-SKK = refl

  nf-SKK∙I : nf (SKK ∙ I {⋆}) ≡ lam (ne (var vz))
  nf-SKK∙I = refl

--
-- Relational big-step semantics.
--

mutual

  infix 4 ⟦_⟧_⇓_ ⟦_⟧*_⇓_ _⟨∙⟩_⇓_

  data ⟦_⟧_⇓_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (u : Val Γ α) → Set where
    ø⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ø ⟧ (u ∷ ρ) ⇓ u
    ∙⇓ : ∀ {α β Γ Δ} {t : Tm Δ (α ⇒ β)} {t′ : Tm Δ α} {ρ : Env Γ Δ} {u v w}
      (p : ⟦ t ⟧ ρ ⇓ u) (q : ⟦ t′ ⟧ ρ ⇓ v) (r : u ⟨∙⟩ v ⇓ w) →
      ⟦ t ∙ t′ ⟧ ρ ⇓ w
    ƛ⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} →
      ⟦ ƛ t ⟧ ρ ⇓ lam t ρ
    []⇓ : ∀ {α Γ Δ Σ} {t : Tm Σ α } {σ : Sub Δ Σ} {ρ : Env Γ Δ} {ρ′ u}
      (p : ⟦ σ ⟧* ρ ⇓ ρ′) (q : ⟦ t ⟧ ρ′ ⇓ u) →
      ⟦ t [ σ ] ⟧ ρ ⇓ u

  data ⟦_⟧*_⇓_ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : Env Γ Δ) (ρ′ : Env Γ Σ) → Set where
    ι⇓ : ∀ {Γ Σ} {ρ : Env Γ Σ} →
      ⟦ ı ⟧* ρ ⇓ ρ
    ⊙⇓ : ∀ {Γ Δ Δ′ Σ} {σ : Sub Δ′ Σ} {σ′ : Sub Δ Δ′} {ρ : Env Γ Δ} {ρ′ ρ′′}
      (p : ⟦ σ′ ⟧* ρ ⇓ ρ′) (q : ⟦ σ ⟧* ρ′ ⇓ ρ′′) →
      ⟦ σ ⊙ σ′ ⟧* ρ ⇓ ρ′′
    ∷⇓ : ∀ {α Γ Δ Σ} {t : Tm Δ α} {σ : Sub Δ Σ} {ρ : Env Γ Δ} {u ρ′}
      (p : ⟦ t ⟧ ρ ⇓ u) (q : ⟦ σ ⟧* ρ ⇓ ρ′) →
      ⟦ t ∷ σ ⟧* ρ ⇓ u ∷ ρ′
    ↑⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ↑ ⟧* (u ∷ ρ) ⇓ ρ

  data _⟨∙⟩_⇓_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) (w : Val Γ β) → Set where
    ne⇓  : ∀ {α β Γ} {us : Ne Val Γ (α ⇒ β)} {u} →
      ne us ⟨∙⟩ u ⇓ ne (app us u)
    lam⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} {u v}
      (p : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v

mutual

  data QVal_⇓_ : ∀ {α Γ} (u : Val Γ α) (n : Nf Γ α) → Set where
    ⋆⇓ : ∀ {Γ} (us : Ne Val Γ ⋆) {ns}
      (p : QNeVal us ⇓ ns) →
      QVal (ne us) ⇓ ne ns
    ⇒⇓ : ∀ {α β Γ} {f : Val Γ (α ⇒ β)} {u n} →
      (p : wkVal f ⟨∙⟩ ne (var vz) ⇓ u) (q : QVal u ⇓ n) →
      QVal f ⇓ lam n

  data QNeVal_⇓_ : ∀ {α Γ} (us : Ne Val Γ α) (ns : Ne Nf Γ α) → Set where
    var⇓ : ∀ {α Γ} {x : Var (α ∷ Γ) α} →
      QNeVal var x ⇓ var x
    app⇓ : ∀ {α β Γ} {us : Ne Val Γ (α ⇒ β)} {u : Val Γ α} {n′ u′}
      (p : QNeVal us ⇓ n′) (q : QVal u ⇓ u′) →
      QNeVal app us u ⇓ app n′ u′


data Nf_⇓_ : ∀ {α Γ} (t : Tm Γ α) (n : Nf Γ α) → Set where
  nf⇓ : ∀ {α Γ} {t : Tm Γ α} {u m}
    (p : ⟦ t ⟧ id-env ⇓ u) (q : QVal u ⇓ m) →
    Nf t ⇓ m

nf-III⇓ : Nf III ⇓ lam (ne (var vz))
nf-III⇓ = nf⇓ (∙⇓ ƛ⇓ (∙⇓ ƛ⇓ ƛ⇓ (lam⇓ ø⇓)) (lam⇓ ø⇓))
                  (⇒⇓ (lam⇓ ø⇓) (⋆⇓ (var vz) var⇓))

--
-- Structurally recursive evaluator.
--

mutual

  infix 4 ⟦_⟧_&_ ⟦_⟧*_&_
  infixl 5 _⟨∙⟩_&_

  ⟦_⟧_&_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) {w : Val Γ α} →
    ⟦ t ⟧ ρ ⇓ w → ∃ λ w′ → w′ ≡ w

  ⟦ ø ⟧ u ∷ ρ & ø⇓ =
    u , refl
  ⟦ t ∙ t′ ⟧ ρ & ∙⇓ ⇓u ⇓v ⇓w with ⟦ t ⟧ ρ & ⇓u | ⟦ t′ ⟧ ρ & ⇓v
  ... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & ⇓w
  ⟦ ƛ t ⟧ ρ & ƛ⇓ =
    lam t ρ , refl
  ⟦ t [ σ ] ⟧ ρ & []⇓ ⇓ρ′ ⇓w with ⟦ σ ⟧* ρ & ⇓ρ′
  ... | ρ′′ , refl = ⟦ t ⟧ ρ′′ & ⇓w

  ⟦_⟧*_&_ : ∀ {B Γ Δ} (σ : Sub Γ Δ) (ρ : Env B Γ) {ρ′ : Env B Δ} →
    ⟦ σ ⟧* ρ ⇓ ρ′ → ∃ λ ρ′′ → ρ′′ ≡ ρ′

  ⟦ ı ⟧* ρ & ι⇓ =
    ρ , refl
  ⟦ σ₁ ⊙ σ₂ ⟧* ρ & ⊙⇓ ⇓ρ₂ ⇓ρ₁ with ⟦ σ₂ ⟧* ρ & ⇓ρ₂
  ... | ρ′′ , refl = ⟦ σ₁ ⟧* ρ′′ & ⇓ρ₁
  ⟦ t ∷ σ ⟧* ρ & ∷⇓ ⇓u ⇓ρ′ with ⟦ t ⟧ ρ & ⇓u | ⟦ σ ⟧* ρ & ⇓ρ′
  ... | u′ , refl | ρ′′ , refl = u′ ∷ ρ′′ , refl
  ⟦ ↑ ⟧* u ∷ ρ & ↑⇓ =
    ρ , refl

  _⟨∙⟩_&_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) {w : Val Γ β} →
    u ⟨∙⟩ v ⇓ w → ∃ λ w′ → w′ ≡ w

  ne us ⟨∙⟩ u & ne⇓ =
    ne (app us u) , refl
  lam t ρ ⟨∙⟩ u & lam⇓ ⇓w =
    ⟦ t ⟧ (u ∷ ρ) & ⇓w

⟦⟧-III : ⟦ III ⟧ id-env & ∙⇓ ƛ⇓ (∙⇓ ƛ⇓ ƛ⇓ (lam⇓ ø⇓)) (lam⇓ ø⇓) ≡
  lam ø [] , refl
⟦⟧-III = refl

--
-- Strong computability.
--


SCV : ∀ {α Γ} (u : Val Γ α) → Set
SCV {⋆} {Γ} (ne us) = ∃ λ (ns : Ne Nf Γ ⋆) →
  QNeVal us ⇓ ns
  × embNeVal us ≈ embNeNf ns
SCV {α ⇒ β} {Γ} u = ∀ {Β} (η : Β ≤ Γ) (v : Val Β α) (q : SCV v) →
  ∃ λ w → (val≤ η u) ⟨∙⟩ v ⇓ w
    × embVal (val≤ η u) ∙ embVal v ≈ embVal w
    × SCV w

SCE : ∀ {Γ Δ} (ρ : Env Γ Δ) → Set
SCE [] = ⊤
SCE (u ∷ ρ) = SCV u × SCE ρ
