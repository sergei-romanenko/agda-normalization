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
{-
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Properties
  using ()
-}
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
    ≃cong⊙ : ∀ {Γ Δ Γ′} {σ₁ σ₂ : Sub Δ Γ} {τ₁ τ₂ : Sub Γ′ Δ} →
      σ₁ ≃ σ₂ → τ₁ ≃ τ₂ → σ₁ ⊙ τ₁ ≃ σ₂ ⊙ τ₂
    ≃cong∷ : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α} {σ₁ σ₂ : Sub Δ Γ} →
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
    ≈cong∙ : ∀ {α β Γ} {t₁ t₂ : Tm Γ (α ⇒ β)} {u₁ u₂ : Tm Γ α} →
      t₁ ≈ t₂ → u₁ ≈ u₂ → t₁ ∙ u₁ ≈ t₂ ∙ u₂
    ≈cong[] : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α } {σ₁ σ₂ : Sub Γ Δ} →
      t₁ ≈ t₂ → σ₁ ≃ σ₂ → t₁ [ σ₁ ] ≈ t₂ [ σ₂ ]
    ≈congƛ : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
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
    ≈βσ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} {t′ : Tm Γ α} →
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
    (ƛ t) [ embEnv ρ ]
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
  ≤[]   : [] ≤ []
  ≤weak : ∀ {α Γ Δ} (η : Γ ≤ Δ) → α ∷ Γ ≤ Δ
  ≤lift : ∀ {α Γ Δ} (η : Γ ≤ Δ) → α ∷ Γ ≤ α ∷ Δ

≤id : ∀ {Γ} → Γ ≤ Γ
≤id {[]} = ≤[]
≤id {α ∷ Γ} = ≤lift ≤id

infixr 6 _●_

_●_ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (η′ : Γ ≤ Δ) → Β ≤ Δ
≤[] ● ≤[] = ≤[]
≤weak η ● η′ = ≤weak (η ● η′)
≤lift η ● ≤weak η′ = ≤weak (η ● η′)
≤lift η ● ≤lift η′ = ≤lift (η ● η′)

≤id●η :  ∀ {Γ Δ} (η : Γ ≤ Δ) → ≤id ● η ≡ η
≤id●η ≤[] = refl
≤id●η (≤weak η) = cong ≤weak (≤id●η η)
≤id●η (≤lift η) = cong ≤lift (≤id●η η)

η●≤id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η ● ≤id ≡ η
η●≤id ≤[] = refl
η●≤id (≤weak η) = cong ≤weak (η●≤id η)
η●≤id (≤lift η) = cong ≤lift (η●≤id η)

assoc● :  ∀ {Β Γ₁ Γ₂ Δ} (η : Β ≤ Γ₁) (η′ : Γ₁ ≤ Γ₂) (η′′ : Γ₂ ≤ Δ) →
  (η ● η′) ● η′′ ≡ η ● (η′ ● η′′)
assoc● ≤[] ≤[] ≤[] = refl
assoc● (≤weak η) η′ η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤weak η′) η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤weak η′′) = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤lift η′′) = cong ≤lift (assoc● η η′ η′′)

--
-- Applying OPEs.
--

var≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (x : Var Δ α) → Var Γ α
var≤ ≤[] x = x
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
-- ≤ to Sub.
--

sub≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) → Sub Γ Δ
sub≤ ≤[] = ı
sub≤ (≤weak η) = sub≤ η ⊙ ↑
sub≤ (≤lift η) = ø ∷ sub≤ η ⊙ ↑

--
-- Applying ≤id.
--

var≤∘≤id : ∀ {α Γ} (x : Var Γ α) → var≤ ≤id x ≡ x
var≤∘≤id vz = refl
var≤∘≤id (vs x) = cong vs (var≤∘≤id x)

mutual

  val≤∘≤id : ∀ {α Γ} (u : Val Γ α) → val≤ ≤id u ≡ u
  val≤∘≤id (ne us) = cong ne (neVal≤∘≤id us)
  val≤∘≤id (lam t ρ) = cong (lam t) (env≤∘≤id ρ)

  neVal≤∘≤id : ∀ {α Γ} (us : Ne Val Γ α) → neVal≤ ≤id us ≡ us
  neVal≤∘≤id (var x) = cong var (var≤∘≤id x)
  neVal≤∘≤id (app us u) = cong₂ app (neVal≤∘≤id us) (val≤∘≤id u)

  env≤∘≤id : ∀ {α Γ} (ρ : Env Γ α) → env≤ ≤id ρ ≡ ρ
  env≤∘≤id [] = refl
  env≤∘≤id (u ∷ ρ) = cong₂ _∷_ (val≤∘≤id u) (env≤∘≤id ρ)

  nf≤∘≤id : ∀ {α Γ} (n : Nf Γ α) → nf≤ ≤id n ≡ n
  nf≤∘≤id (ne ns) = cong ne (neNf≤∘≤id ns)
  nf≤∘≤id (lam n) = cong lam (nf≤∘≤id n)

  neNf≤∘≤id : ∀ {α Γ} (ns : Ne Nf Γ α) → neNf≤ ≤id ns ≡ ns
  neNf≤∘≤id (var x) = cong var (var≤∘≤id x)
  neNf≤∘≤id (app ns u) = cong₂ app (neNf≤∘≤id ns) (nf≤∘≤id u)

--
-- sub≤ ≤id ≃ ı
--

ı≃sub≤-≤id : ∀ {Γ} → sub≤ {Γ} ≤id ≃ ı
ı≃sub≤-≤id {[]} = ≃refl
ı≃sub≤-≤id {α ∷ Γ} = begin
  ø ∷ sub≤ ≤id ⊙ ↑
    ≈⟨ ≃cong∷ ≈refl (≃cong⊙ ı≃sub≤-≤id ≃refl) ⟩
  ø ∷ ı ⊙ ↑
    ≈⟨ ≃sym ≃id∷ ⟩
  ı
  ∎
  where open ≃-Reasoning

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

--
-- Identity environments.
--

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
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓v : ⟦ t′ ⟧ ρ ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w) →
      ⟦ t ∙ t′ ⟧ ρ ⇓ w
    ƛ⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} →
      ⟦ ƛ t ⟧ ρ ⇓ lam t ρ
    []⇓ : ∀ {α Γ Δ Σ} {t : Tm Σ α } {σ : Sub Δ Σ} {ρ : Env Γ Δ} {ρ′ u}
      (⇓ρ′ : ⟦ σ ⟧* ρ ⇓ ρ′) (⇓u : ⟦ t ⟧ ρ′ ⇓ u) →
      ⟦ t [ σ ] ⟧ ρ ⇓ u

  data ⟦_⟧*_⇓_ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : Env Γ Δ) (ρ′ : Env Γ Σ) →
       Set where
    ι⇓ : ∀ {Γ Σ} {ρ : Env Γ Σ} →
      ⟦ ı ⟧* ρ ⇓ ρ
    ⊙⇓ : ∀ {Γ Δ Δ′ Σ} {σ : Sub Δ′ Σ} {σ′ : Sub Δ Δ′} {ρ : Env Γ Δ} {ρ′ ρ′′}
      (⇓ρ′ : ⟦ σ′ ⟧* ρ ⇓ ρ′) (⇓ρ′′ : ⟦ σ ⟧* ρ′ ⇓ ρ′′) →
      ⟦ σ ⊙ σ′ ⟧* ρ ⇓ ρ′′
    ∷⇓ : ∀ {α Γ Δ Σ} {t : Tm Δ α} {σ : Sub Δ Σ} {ρ : Env Γ Δ} {u ρ′}
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓ρ′ : ⟦ σ ⟧* ρ ⇓ ρ′) →
      ⟦ t ∷ σ ⟧* ρ ⇓ u ∷ ρ′
    ↑⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ↑ ⟧* (u ∷ ρ) ⇓ ρ

  data _⟨∙⟩_⇓_ : ∀ {α β Γ}
       (u : Val Γ (α ⇒ β)) (v : Val Γ α) (w : Val Γ β) → Set where
    ne⇓  : ∀ {α β Γ} {us : Ne Val Γ (α ⇒ β)} {u} →
      ne us ⟨∙⟩ u ⇓ ne (app us u)
    lam⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} {u v}
      (⇓v : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v

mutual

  data QVal_⇓_ : ∀ {α Γ} (u : Val Γ α) (n : Nf Γ α) → Set where
    ⋆⇓ : ∀ {Γ} (us : Ne Val Γ ⋆) {ns}
      (⇓ns : QNeVal us ⇓ ns) →
      QVal (ne us) ⇓ ne ns
    ⇒⇓ : ∀ {α β Γ} {f : Val Γ (α ⇒ β)} {u n} →
      (⇓u : wkVal f ⟨∙⟩ ne (var vz) ⇓ u) (⇓n : QVal u ⇓ n) →
      QVal f ⇓ lam n

  data QNeVal_⇓_ : ∀ {α Γ} (us : Ne Val Γ α) (ns : Ne Nf Γ α) → Set where
    var⇓ : ∀ {α Γ} {x : Var Γ α} →
      QNeVal var x ⇓ var x
    app⇓ : ∀ {α β Γ} {us : Ne Val Γ (α ⇒ β)} {u : Val Γ α} {ns n}
      (⇓ns : QNeVal us ⇓ ns) (⇓n : QVal u ⇓ n) →
      QNeVal app us u ⇓ app ns n


data Nf_⇓_ : ∀ {α Γ} (t : Tm Γ α) (n : Nf Γ α) → Set where
  nf⇓ : ∀ {α Γ} {t : Tm Γ α} {u n}
    (⇓u : ⟦ t ⟧ id-env ⇓ u) (⇓n : QVal u ⇓ n) →
    Nf t ⇓ n

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
-- Composing OPEs.
--

var≤-≤id : ∀ {α Γ}(x : Var Γ α) → var≤ ≤id x ≡ x
var≤-≤id vz = refl
var≤-≤id (vs x) = cong vs (var≤-≤id x)


-- Variables.

var≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
  (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (x : Var Γ₃ α) →
  var≤ η (var≤ η′ x) ≡ var≤ (η ● η′) x
var≤∘ ≤[] ≤[] x = refl
var≤∘ (≤weak η) η′ x = cong vs (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤weak η′) x = cong vs (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤lift η′) vz = refl
var≤∘ (≤lift η) (≤lift η′) (vs x) = cong vs (var≤∘ η η′ x)

-- Values and environments.

mutual

  val≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (u : Val Γ₃ α) →
    val≤ η (val≤ η′ u) ≡ val≤ (η ● η′) u
  val≤∘ η η′ (ne us) = cong ne (neVal≤∘ η η′ us)
  val≤∘ η η′ (lam t ρ) = cong (lam t) (env≤∘ η η′ ρ)

  neVal≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (us : Ne Val Γ₃ α) →
    neVal≤ η (neVal≤ η′ us) ≡ neVal≤ (η ● η′) us
  neVal≤∘ η η′ (var x) =
    cong var (var≤∘ η η′ x)
  neVal≤∘ η η′ (app us u) =
    cong₂ app (neVal≤∘ η η′ us) (val≤∘ η η′ u)

  env≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (ρ : Env Γ₃ α) →
    env≤ η (env≤ η′ ρ) ≡ env≤ (η ● η′) ρ
  env≤∘ η η′ [] = refl
  env≤∘ η η′ (u ∷ ρ) =
    cong₂ _∷_ (val≤∘ η η′ u) (env≤∘ η η′ ρ)

--
-- OPEs commute with evaluation
--

mutual

  ⟦⟧⇓≤ : ∀ {α Β Γ Δ} (η : Β ≤ Γ) {t : Tm Δ α} {ρ : Env Γ Δ} {u : Val Γ α}
    (⇓u : ⟦ t ⟧ ρ ⇓ u) →
    ⟦ t ⟧ env≤ η ρ ⇓ val≤ η u
  ⟦⟧⇓≤ η ø⇓ = ø⇓
  ⟦⟧⇓≤ η (∙⇓ ⇓u ⇓v ⇓w) = ∙⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧⇓≤ η ⇓v) (⟨∙⟩⇓≤ η ⇓w)
  ⟦⟧⇓≤ η ƛ⇓ = ƛ⇓
  ⟦⟧⇓≤ η ([]⇓ ⇓ρ′ ⇓u) = []⇓ (⟦⟧*⇓≤ η ⇓ρ′) (⟦⟧⇓≤ η ⇓u)

  ⟦⟧*⇓≤ : ∀ {Β Γ Δ Δ′} (η : Β ≤ Γ) {σ : Sub Δ′ Δ} {ρ : Env Γ Δ′} {ρ′ : Env Γ Δ}
    (⇓ρ′ : ⟦ σ ⟧* ρ ⇓ ρ′) →
    ⟦ σ ⟧* env≤ η ρ ⇓ env≤ η ρ′
  ⟦⟧*⇓≤ η ι⇓ = ι⇓
  ⟦⟧*⇓≤ η (⊙⇓ ⇓ρ′ ⇓ρ′′) = ⊙⇓ (⟦⟧*⇓≤ η ⇓ρ′) (⟦⟧*⇓≤ η ⇓ρ′′)
  ⟦⟧*⇓≤ η (∷⇓ ⇓u ⇓ρ′) = ∷⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧*⇓≤ η ⇓ρ′)
  ⟦⟧*⇓≤ η ↑⇓ = ↑⇓

  ⟨∙⟩⇓≤ : ∀ {α β Β Γ} (η : Β ≤ Γ)
    {u : Val Γ (α ⇒ β)} {v : Val Γ α} {w : Val Γ β}
    (⇓w : u ⟨∙⟩ v ⇓ w) →
    val≤ η u ⟨∙⟩ val≤ η v ⇓ val≤ η w
  ⟨∙⟩⇓≤ η ne⇓ = ne⇓
  ⟨∙⟩⇓≤ η (lam⇓ ⇓v) = lam⇓ (⟦⟧⇓≤ η ⇓v)

--
-- OPEs commute with wkVal.
--

wkVal∘val≤ : ∀ {Β Γ α β} (η : Β ≤ Γ) (u : Val Γ α) →
  wkVal (val≤ η u) ≡ val≤ (≤lift {β} η) (wkVal u)
wkVal∘val≤ η u = begin
  wkVal (val≤ η u)
    ≡⟨⟩
  val≤ (≤weak ≤id) (val≤ η u)
    ≡⟨ val≤∘ (≤weak ≤id) η u ⟩
  val≤ (≤weak (≤id ● η)) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (≤id●η η) ⟩
  val≤ (≤weak η) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (sym $ η●≤id η) ⟩
  val≤ (≤weak (η ● ≤id)) u
    ≡⟨⟩
  val≤ (≤lift η ● ≤weak ≤id) u
    ≡⟨ sym $ val≤∘ (≤lift η) (≤weak ≤id) u ⟩
  val≤ (≤lift η) (val≤ (≤weak ≤id) u)
    ≡⟨⟩
  val≤ (≤lift η) (wkVal u)
  ∎
  where open ≡-Reasoning

--
-- OPEs commute with embeddings.
--

embVar∘≤ :  ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  embVar (var≤ η x) ≈ embVar x [ sub≤ η ]
embVar∘≤ ≤[] x = ≈sym ≈id
embVar∘≤ (≤weak η) vz = begin
  embVar (var≤ (≤weak η) vz)
    ≡⟨⟩
  embVar (var≤ η vz) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η vz) ≃refl ⟩
  ø [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  ø [ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar vz [ sub≤ (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤weak η) (vs x) = begin
  embVar (var≤ (≤weak η) (vs x))
    ≡⟨⟩
  embVar (var≤ η (vs x)) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η (vs x)) ≃refl ⟩
  embVar x [ ↑ ] [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  embVar x [ ↑ ] [ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar (vs x) [ sub≤ (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) vz = begin
  embVar (var≤ (≤lift η) vz)
    ≡⟨⟩
  ø
    ≈⟨ ≈sym ≈proj ⟩
  ø [ ø ∷ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar vz [ sub≤ (≤lift η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) (vs x) = begin
  embVar (var≤ (≤lift η) (vs x))
    ≡⟨⟩
  embVar (var≤ η x) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η x) ≃refl ⟩
  embVar x [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  embVar x [ sub≤ η ⊙ ↑ ]
    ≈⟨ ≈cong[] ≈refl (≃sym ≃wk) ⟩
  embVar x [ ↑ ⊙ (ø ∷ sub≤ η ⊙ ↑) ]
    ≈⟨ ≈comp ⟩
  embVar x [ ↑ ] [ ø ∷ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar (vs x) [ sub≤ (≤lift η) ]
  ∎
  where open ≈-Reasoning

mutual

  embVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (u : Val Γ α) →
    embVal (val≤ η u) ≈ embVal u [ sub≤ η ]
  embVal∘≤ η (ne us) = embNeVal∘≤ η us
  embVal∘≤ η (lam t ρ) = begin
    embVal (val≤ η (lam t ρ))
      ≡⟨⟩
    (ƛ t) [ embEnv (env≤ η ρ) ]
      ≈⟨ ≈cong[] ≈refl (embEnv∘≤ η ρ) ⟩
    (ƛ t) [ embEnv ρ ⊙ sub≤ η ]
      ≈⟨ ≈comp  ⟩
    (ƛ t) [ embEnv ρ ] [ sub≤ η ]
      ≡⟨⟩
    embVal (lam t ρ) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embNeVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : Ne Val Γ α) →
    embNeVal (neVal≤ η us) ≈ embNeVal us [ sub≤ η ]
  embNeVal∘≤ η (var x) = embVar∘≤ η x
  embNeVal∘≤ η (app us u) = begin
    embNeVal (neVal≤ η (app us u))
      ≡⟨⟩
    embNeVal (neVal≤ η us) ∙ embVal (val≤ η u)
      ≈⟨ ≈cong∙ (embNeVal∘≤ η us) (embVal∘≤ η u) ⟩
    embNeVal us [ sub≤ η ] ∙ embVal u [ sub≤ η ]
      ≈⟨ ≈sym ≈app ⟩
    (embNeVal us ∙ embVal u) [ sub≤ η ]
      ≡⟨⟩
    embNeVal (app us u) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embEnv∘≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (ρ : Env Γ Δ) →
    embEnv (env≤ η ρ) ≃ embEnv ρ ⊙ sub≤ η
  embEnv∘≤ ≤[] [] = ≃sym ≃idr
  embEnv∘≤ {Γ = []} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≃cong⊙ (embEnv∘≤ η []) ≃refl ⟩
    (ı ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≃assoc ⟩
    ı ⊙ sub≤ η ⊙ ↑
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤weak η)
    ∎
    where open ≃-Reasoning
  embEnv∘≤ {Γ = α ∷ Γ} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≃cong⊙ (embEnv∘≤ η []) ≃refl ⟩
    ((sub-from-[] ⊙ ↑) ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≃assoc ⟩
    (sub-from-[] ⊙ ↑) ⊙ (sub≤ η ⊙ ↑)
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤weak η)
    ∎
    where open ≃-Reasoning
  embEnv∘≤ (≤lift η) [] = begin
    embEnv (env≤ (≤lift η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≃cong⊙ (embEnv∘≤ η []) ≃refl ⟩
    (sub-from-[] ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≃assoc ⟩
    sub-from-[] ⊙ (sub≤ η ⊙ ↑)
      ≈⟨ ≃cong⊙ ≃refl (≃sym ≃wk) ⟩
    sub-from-[] ⊙ (↑ ⊙ (ø ∷ sub≤ η ⊙ ↑))
      ≈⟨ ≃sym ≃assoc ⟩
    (sub-from-[] ⊙ ↑) ⊙ (ø ∷ sub≤ η ⊙ ↑)
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤lift η)
    ∎
    where open ≃-Reasoning
  embEnv∘≤ η (u ∷ ρ) = begin
    embEnv (env≤ η (u ∷ ρ))
      ≡⟨⟩
    embVal (val≤ η u) ∷ embEnv (env≤ η ρ)
      ≈⟨ ≃cong∷ (embVal∘≤ η u) (embEnv∘≤ η ρ) ⟩
    embVal u [ sub≤ η ] ∷ embEnv ρ ⊙ sub≤ η
      ≈⟨ ≃sym ≃cons ⟩
    (embVal u ∷ embEnv ρ) ⊙ sub≤ η
      ≡⟨⟩
    embEnv (u ∷ ρ) ⊙ sub≤ η
    ∎
    where open ≃-Reasoning

-- Normal forms.

mutual

  embNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (n : Nf Γ α) →
    embNf (nf≤ η n) ≈ embNf n [ sub≤ η ]
  embNf∘≤ η (ne ns) = embNeNf∘≤ η ns
  embNf∘≤ η (lam n) = begin
    embNf (nf≤ η (lam n))
      ≡⟨⟩
    ƛ embNf (nf≤ (≤lift η) n)
      ≈⟨ ≈congƛ (embNf∘≤ (≤lift η) n) ⟩
    ƛ embNf n [ ø ∷ sub≤ η ⊙ ↑ ]
      ≈⟨ ≈sym ≈lam ⟩
    (ƛ embNf n) [ sub≤ η ]
      ≡⟨⟩
    embNf (lam n) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embNeNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (ns : Ne Nf Γ α) →
    embNeNf (neNf≤ η ns) ≈ embNeNf ns [ sub≤ η ]
  embNeNf∘≤ η (var x) = embVar∘≤ η x
  embNeNf∘≤ η (app ns u) = begin
    embNeNf (neNf≤ η (app ns u))
      ≡⟨⟩
    embNeNf (neNf≤ η ns) ∙ embNf (nf≤ η u)
      ≈⟨ ≈cong∙ (embNeNf∘≤ η ns) (embNf∘≤ η u) ⟩
    (embNeNf ns [ sub≤ η ]) ∙ (embNf u [ sub≤ η ])
      ≈⟨ ≈sym ≈app ⟩
    (embNeNf ns ∙ embNf u) [ sub≤ η ]
      ≡⟨⟩
    embNeNf (app ns u) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

mutual

  qVal≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {u : Val Γ α} {n : Nf Γ α}
    (⇓n : QVal u ⇓ n) →
      QVal val≤ η u ⇓ nf≤ η n

  qVal≤ η (⋆⇓ us ⇓ns) =
    ⋆⇓ (neVal≤ η us) (qNeVal≤ η ⇓ns)
  qVal≤ η (⇒⇓ {f = f} {u} {n} ⇓u ⇓n) =
    ⇒⇓ ⇓u′′′ ⇓n′
    where
      ⇓u′ : val≤ (≤lift η) (wkVal f) ⟨∙⟩ ne (var vz) ⇓ val≤ (≤lift η) u
      ⇓u′ = ⟨∙⟩⇓≤ (≤lift η) ⇓u
      ⇓u′′′ : wkVal (val≤ η f) ⟨∙⟩ ne (var vz) ⇓ val≤ (≤lift η) u
      ⇓u′′′ = subst (λ w → w ⟨∙⟩ ne (var vz) ⇓ val≤ (≤lift η) u)
                    (sym $ wkVal∘val≤ η f) ⇓u′
      ⇓n′ : QVal val≤ (≤lift η) u ⇓ nf≤ (≤lift η) n
      ⇓n′ = qVal≤ (≤lift η) ⇓n

  qNeVal≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {us : Ne Val Γ α} {ns : Ne Nf Γ α}
    (⇓ns : QNeVal us ⇓ ns) →
      QNeVal neVal≤ η us ⇓ neNf≤ η ns

  qNeVal≤ η var⇓ = var⇓
  qNeVal≤ η (app⇓ ⇓ns ⇓n) =
    app⇓ (qNeVal≤ η ⇓ns) (qVal≤ η ⇓n)



embNe≈≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : Ne Val Γ α) (ns : Ne Nf Γ α) →
  (p : embNeVal us ≈ embNeNf ns) →
     embNeVal (neVal≤ η us) ≈ embNeNf (neNf≤ η ns)
embNe≈≤ η us ns p = begin
  embNeVal (neVal≤ η us)
    ≈⟨ embNeVal∘≤ η us ⟩
  embNeVal us [ sub≤ η ]
    ≈⟨ ≈cong[] p ≃refl ⟩
  embNeNf ns [ sub≤ η ]
    ≈⟨ ≈sym (embNeNf∘≤ η ns) ⟩
  embNeNf (neNf≤ η ns)
  ∎
  where open ≈-Reasoning

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

--
-- Weakening for SCV & SCE.
--
-- (p : SCV u) → ∀ {Β} (η : Β ≤ Γ) → SCV (val≤ η u)
-- (r : SCE ρ) → ∀ {Β} (η : Β ≤ Γ) → SCE (env≤ η ρ)
--

mutual

  scv≤ :  ∀ {α Γ} (u : Val Γ α) (p : SCV u) →
    ∀ {Β} (η : Β ≤ Γ) → SCV (val≤ η u)
  scv≤ {⋆} (ne us) (ns , p , q) η =
    neNf≤ η ns , qNeVal≤ η p , embNe≈≤ η us ns q
  scv≤ {α ⇒ β} {Γ} u p {Β} η {Β′} η′ v q with p (η′ ● η) v q
  ... | w , ●⇓w , ●≈w , r =
    w , ∘⇓w , ∘≈w≤ , r
    where
    open ≈-Reasoning
    ∘≡● : val≤ η′ (val≤ η u) ≡ val≤ (η′ ● η) u
    ∘≡● = val≤∘ η′ η u
    ∘⇓w : val≤ η′ (val≤ η u) ⟨∙⟩ v ⇓ w
    ∘⇓w = subst (λ f → f ⟨∙⟩ v ⇓ w) (sym $ ∘≡●) ●⇓w
    ∘≈w≤ : embVal (val≤ η′ (val≤ η u)) ∙ embVal v ≈ embVal w
    ∘≈w≤ = begin
      embVal (val≤ η′ (val≤ η u)) ∙ embVal v
        ≡⟨ cong₂ _∙_ (cong embVal (val≤∘ η′ η u)) refl ⟩
      embVal (val≤ (η′ ● η) u) ∙ embVal v
        ≈⟨ ●≈w ⟩
      embVal w
      ∎

  sce≤ : ∀ {Γ Δ} (ρ : Env Γ Δ) (r : SCE ρ) →
    ∀ {Β} (η : Β ≤ Γ) → SCE (env≤ η ρ)
  sce≤ [] r η = tt
  sce≤ (u ∷ ρ) (p , r) η = scv≤ u p η , sce≤ ρ r η

--
-- embVal (wkVal u) ≈ embVal u [ ↑ ]
--

embVal∘wkVal : ∀ {α γ Γ} (u : Val Γ α) →
  embVal (wkVal {α} u) ≈ embVal u [ ↑ {γ} ]
embVal∘wkVal u = begin
  embVal (wkVal u)
    ≡⟨⟩
  embVal (val≤ wk u)
    ≈⟨ embVal∘≤ wk u ⟩
  embVal u [ sub≤ ≤id ⊙ ↑ ]
    ≈⟨ ≈cong[] ≈refl (≃cong⊙ ı≃sub≤-≤id ≃refl) ⟩
  {-
    ≈⟨ embVal∘≤ wk u ⟩
  embVal u [ ı ⊙ ↑ ]
    ≈⟨ ≈cong[] ≈refl ≃idl ⟩
  -}
  embVal u [ ı ⊙ ↑ ]
    ≈⟨ ≈cong[] ≈refl ≃idl ⟩
  embVal u [ ↑ ]
  ∎
  where open ≈-Reasoning


--
-- ∃ λ n → QVal u ⇓ n × embVal u ≈ embNf n
-- QNeVal us ⇓ ns → embNeVal us ≈ embNeNf ns → SCV (ne us)
--

mutual

  scv→val⇓ : ∀ {α Γ} (u : Val Γ α) (p : SCV u) →
    ∃ λ n → QVal u ⇓ n × embVal u ≈ embNf n
  scv→val⇓ {⋆} (ne us) (ns , ⇓ns , ≈ns) =
    ne ns , ⋆⇓ us ⇓ns , ≈ns
  scv→val⇓ {α ⇒ β} {Γ} u p
    with neVal⇓→scv {α} {α ∷ Γ} (var vz) (var vz) var⇓ ≈refl
  ... | r with p wk (ne (var vz)) r
  ... | v , ⇓v , ≈v , q with scv→val⇓ {β} v q
  ... | m , ⇓m , ≈m =
    lam m , ⇒⇓ ⇓v ⇓m , u≈m
    where
    open ≈-Reasoning
    u≈m : embVal u ≈ embNf (lam m)
    u≈m = begin
      embVal u
        ≈⟨ ≈η ⟩
      ƛ embVal u [ ↑ ] ∙ ø
        ≈⟨ ≈congƛ (≈cong∙ (≈sym (embVal∘wkVal u)) ≈refl) ⟩
      ƛ embVal (wkVal u) ∙ ø
        ≈⟨ ≈congƛ ≈v ⟩
      ƛ embVal v
        ≈⟨ ≈congƛ ≈m ⟩
      ƛ embNf m
        ≡⟨⟩
      embNf (lam m)
      ∎
          
  neVal⇓→scv : ∀ {α Γ} (us : Ne Val Γ α) (ns : Ne Nf Γ α) →
    QNeVal us ⇓ ns → embNeVal us ≈ embNeNf ns → SCV (ne us)
  neVal⇓→scv {⋆} us ns ⇓ns ≈ns =
    ns , ⇓ns , ≈ns
  neVal⇓→scv {α ⇒ β} {Γ} us ns ⇓ns ≈ns {Β} η u p with  scv→val⇓ u p
  ... | m , ⇓m , u≈m =
    ne (app us≤ u) , ne⇓ , ≈refl , r
    where
    open ≈-Reasoning

    us≤ : Ne Val Β (α ⇒ β)
    us≤ = neVal≤ η us

    ns≤ : Ne Nf Β (α ⇒ β)
    ns≤ = neNf≤ η ns

    us∙u≈ns∙m = begin
      embNeVal us≤ ∙ embVal u
        ≈⟨ ≈cong∙ (embNe≈≤ η us ns ≈ns) u≈m ⟩
      embNeNf ns≤ ∙ embNf m ∎

    r : SCV (ne (app us≤ u))
    r = neVal⇓→scv (app us≤ u) (app ns≤ m)
                        (app⇓ (qNeVal≤ η ⇓ns) ⇓m) us∙u≈ns∙m

embEnv∘id-env : ∀ {Γ} → embEnv (id-env {Γ}) ≃ ı
embEnv∘id-env {[]} = ≃refl
embEnv∘id-env {x ∷ Γ} = begin
  ø ∷ embEnv (wkEnv id-env)
    ≡⟨⟩
  ø ∷ embEnv (env≤ wk id-env)
    ≈⟨ ≃cong∷ ≈refl (embEnv∘≤ wk id-env) ⟩
  ø ∷ embEnv id-env ⊙ (sub≤ ≤id ⊙ ↑)
    ≈⟨ ≃cong∷ ≈refl (≃cong⊙ ≃refl (≃cong⊙ ı≃sub≤-≤id ≃refl)) ⟩
  ø ∷ embEnv id-env ⊙ (ı ⊙ ↑)
    ≈⟨ ≃cong∷ ≈refl (≃cong⊙ embEnv∘id-env ≃idl) ⟩
  ø ∷ (ı ⊙ ↑)
    ≈⟨ ≃sym ≃id∷ ⟩
  ı ∎
  where open ≃-Reasoning

-- SCE id-env

scv-var : ∀ {α Γ} (x : Var Γ α) → SCV (ne (var x))
scv-var x = neVal⇓→scv (var x) (var x) var⇓ ≈refl

sce-id-env : ∀ {Γ} → SCE (id-env {Γ})
sce-id-env {[]} = tt
sce-id-env {α ∷ Γ} = scv-var vz , sce≤ id-env sce-id-env wk

--
-- The fundamental theorem about strong computability:
-- all terms are "strongly computable".
--

mutual

  all-scv : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (r : SCE ρ) →
    ∃ λ u → ⟦ t ⟧ ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u) × SCV u

  all-scv ø (u ∷ ρ) (p , r) =
    u , ø⇓ , ≈proj , p
  all-scv {β} {Γ} {Δ} (t ∙ t′) ρ r with all-scv t ρ r | all-scv t′ ρ r
  ... | u , ⇓u , ≈u , p | v , ⇓v , ≈v , q with p ≤id v q
  ... | w , ⇓w , ≈w , r′ =
    w , ∙⇓ ⇓u ⇓v ⇓w′ , ≈w′ , r′
    where
    open ≈-Reasoning
    ⇓w′ : u ⟨∙⟩ v ⇓ w
    ⇓w′ = subst (λ u′ → u′ ⟨∙⟩ v ⇓ w) (val≤∘≤id u) ⇓w
    ≈w′ : (t ∙ t′) [ embEnv ρ ] ≈ embVal w
    ≈w′ = begin
      (t ∙ t′) [ embEnv ρ ]
        ≈⟨ ≈app ⟩
      t [ embEnv ρ ] ∙ t′ [ embEnv ρ ]
        ≈⟨ ≈cong∙ ≈u ≈v ⟩
      embVal u ∙ embVal v
        ≡⟨ cong₂ _∙_ (cong embVal (sym $ val≤∘≤id u)) refl ⟩
      embVal (val≤ ≤id u) ∙ embVal v
        ≈⟨ ≈w ⟩
      embVal w
      ∎
  all-scv (ƛ t) ρ r =
    lam t ρ , ƛ⇓ , ≈refl , r′
    where
    r′ : SCV (lam t ρ)
    r′ η u p with all-scv t (u ∷ env≤ η ρ) (p , sce≤ ρ r η)
    ... | v , ∷⇓v , ≈v , q =
      v , lam⇓ ∷⇓v , ≈v′ , q
      where
      open ≈-Reasoning
      ≈v′ : (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u ≈ embVal v
      ≈v′ = begin
        (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u
          ≈⟨ ≈βσ ⟩
        t [ embVal u ∷ embEnv (env≤ η ρ) ]
          ≈⟨ ≈v ⟩
        embVal v
        ∎
  all-scv (t [ σ ]) ρ r with all-sce σ ρ r
  ... | ρ′ , ⇓ρ′ , ≃ρ′ , r′ with all-scv t ρ′ r′
  ... | u , ⇓u , ≈u , p =
    u , ⇓u′ , ≈u′ , p
    where
    open ≈-Reasoning
    ⇓u′ : ⟦ t [ σ ] ⟧ ρ ⇓ u
    ⇓u′ = []⇓ ⇓ρ′ ⇓u
    ≈u′ : t [ σ ] [ embEnv ρ ] ≈ embVal u
    ≈u′ = begin
      t [ σ ] [ embEnv ρ ]
        ≈⟨ ≈sym ≈comp ⟩
      t [ σ ⊙ embEnv ρ ]
        ≈⟨ ≈cong[] ≈refl ≃ρ′ ⟩
      t [ embEnv ρ′ ]
        ≈⟨ ≈u ⟩
      embVal u
      ∎

  all-sce : ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ) (r : SCE ρ) →
    ∃ λ ρ′ → ⟦ σ ⟧* ρ ⇓ ρ′ × (σ ⊙ embEnv ρ ≃ embEnv ρ′) × SCE ρ′

  all-sce ı ρ r =
    ρ , ι⇓ , ≃idl , r
  all-sce (σ ⊙ σ′) ρ r with all-sce σ′ ρ r
  ... | ρ′ , ⇓ρ′ , ≃ρ′ , r′ with all-sce σ ρ′ r′
  ... | ρ′′ , ⇓ρ′′ , ≃ρ′′ , r′′ =
    ρ′′ , ⊙⇓ ⇓ρ′ ⇓ρ′′ , ≃ρ′′′ , r′′
    where
    open ≃-Reasoning
    ≃ρ′′′ : (σ ⊙ σ′) ⊙ embEnv ρ ≃ embEnv ρ′′
    ≃ρ′′′ = begin
      (σ ⊙ σ′) ⊙ embEnv ρ
        ≈⟨ ≃assoc ⟩
      σ ⊙ (σ′ ⊙ embEnv ρ)
        ≈⟨ ≃cong⊙ ≃refl ≃ρ′ ⟩
      σ ⊙ embEnv ρ′
        ≈⟨ ≃ρ′′ ⟩
      embEnv ρ′′
      ∎
  all-sce (t ∷ σ) ρ r with all-scv t ρ r | all-sce σ ρ r
  ... | u , ⇓u , ≈u , p | ρ′ , ⇓ρ′ , ≃ρ′ , r′ =
    u ∷ ρ′ , ∷⇓ ⇓u ⇓ρ′ , ≃u∷ρ′ , (p , r′)
    where
    open ≃-Reasoning
    ≃u∷ρ′ : (t ∷ σ) ⊙ embEnv ρ ≃ embVal u ∷ embEnv ρ′
    ≃u∷ρ′ = begin
      (t ∷ σ) ⊙ embEnv ρ
        ≈⟨ ≃cons ⟩
      t [ embEnv ρ ] ∷ (σ ⊙ embEnv ρ)
        ≈⟨ ≃cong∷ ≈u ≃refl ⟩
      embVal u ∷ (σ ⊙ embEnv ρ)
        ≈⟨ ≃cong∷ ≈refl ≃ρ′ ⟩
      embVal u ∷ embEnv ρ′
      ∎
  all-sce ↑ (u ∷ ρ) (p , r) =
    ρ , ↑⇓ , ≃wk , r

--
-- All terms are normalizable.
--

postulate
  all-nf : ∀ {α Γ} (t : Tm Γ α) →
    ∃ λ n → Nf t ⇓ n × (t ≈ embNf n)

--
-- Normalizer!
--

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf t with all-scv t id-env sce-id-env
... | u , ⇓u , ≈u , p with scv→val⇓ u p
... | n , ⇓n , ≈n
  = n

--
-- Completeness: terms are convertible to their normal forms.
--

complete : ∀ {α Γ} (t : Tm Γ α) → t ≈ embNf (nf t)

complete t with all-scv t id-env sce-id-env
... | u , ⇓u , ≈u , p with scv→val⇓ u p
... | n , ⇓n , ≈n = begin
  t
    ≈⟨ ≈sym ≈id ⟩
  t [ ı ]
    ≈⟨ ≈cong[] ≈refl (≃sym embEnv∘id-env) ⟩
  t [ embEnv id-env ]
    ≈⟨ ≈u ⟩
  embVal u
    ≈⟨ ≈n ⟩
  embNf n
  ∎
  where open ≈-Reasoning

--
-- Stability: 
--

postulate

  stable : ∀ {α Γ} (n : Nf Γ α) → nf (embNf n) ≡ n

--
-- Soundness normalisation takes convertible terms to identical
-- normal forms.
--

postulate
  sound : ∀ {α Γ} (t t' : Tm Γ α) → t ≈ t' → nf t ≡ nf t'
