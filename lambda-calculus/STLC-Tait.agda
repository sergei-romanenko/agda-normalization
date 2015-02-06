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

module STLC-Tait where

open import Data.List
  hiding ([_])
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
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
  infixr 4 _⇉_
  infixr 3 ƛ_

  -- Terms.

  data Tm : Ctx → Ty → Set where
    ø   : ∀ {α Γ} → Tm (α ∷ Γ) α
    _∙_ : ∀ {α β Γ} → Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β
    ƛ_  : ∀ {α β Γ} → Tm (α ∷ Γ) β → Tm Γ (α ⇒ β)
    _[_] : ∀ {α Δ Γ} → Tm Δ α → Δ ⇉ Γ → Tm Γ α

  -- Substitutions: `Δ ⇉ Γ` transforms `Tm Δ α` into `Tm Γ α`.

  data _⇉_ : Ctx → Ctx → Set where
    ı   : ∀ {Γ} → Γ ⇉ Γ
    _⊙_ : ∀ {Σ Δ Γ} (σ : Σ ⇉ Δ) (σ′ : Δ ⇉ Γ) → Σ ⇉ Γ
    _∷_ : ∀ {α Δ Γ} (t : Tm Γ α) (σ : Δ ⇉ Γ) → α ∷ Δ ⇉ Γ
    ↑  : ∀ {α Γ} → Γ ⇉ α ∷ Γ


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
-- Weak head normal forms.
--

data Var : Ctx → Ty → Set where
  vz : ∀ {α Γ} → Var (α ∷ Γ) α
  vs  : ∀ {α β Γ} → Var Γ β → Var (α ∷ Γ) β

data Ne (T : Ctx → Ty → Set) : Ctx → Ty → Set where
  var : ∀ {α Γ} (x : Var Γ α) → Ne T Γ α
  app : ∀ {α β Γ} (f : Ne T Γ (α ⇒ β)) (u : T Γ α) → Ne T Γ β


mutual

  data Val : Ctx → Ty → Set where
    lam : ∀ {α β Δ Γ} (t : Tm (α ∷ Δ) β) (ρ : Env Δ Γ) → Val Γ (α ⇒ β)
    ne  : ∀ {α Γ} (n : Ne Val Γ α) → Val Γ α

  data Env : Ctx → Ctx → Set where
    []  : ∀ {Γ} → Env [] Γ
    _∷_ : ∀ {α Δ Γ} (u : Val Γ α) (ρ : Env Δ Γ) → Env (α ∷ Δ) Γ


module NaiveNorm where

  {-# TERMINATING #-}
  mutual

    infixl 5 _⟨∙⟩_

    ⟦_⟧_ : ∀ {α Δ Γ} → Tm Δ α → Env Δ Γ → Val Γ α
    ⟦ ø ⟧ (u ∷ ρ) = u
    ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
    ⟦ ƛ t ⟧ ρ = lam t ρ
    ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

    ⟦_⟧*_ : ∀ {Σ Δ Γ} → Σ ⇉ Δ → Env Δ Γ → Env Σ Γ
    ⟦ ı ⟧* ρ = ρ
    ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
    ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
    ⟦ ↑ ⟧* (u ∷ ρ) = ρ

    _⟨∙⟩_ : ∀ {α β Γ} → Val Γ (α ⇒ β) → Val Γ α → Val Γ β
    lam t ρ ⟨∙⟩ v = ⟦ t ⟧ (v ∷ ρ)
    ne n ⟨∙⟩ v = ne (app n v)

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

  data DEnv : Ctx → Ctx → Set where
    []  : ∀ {Γ} → DEnv [] Γ
    _∷_ : ∀ {α Δ Γ} (u : D α) (ρ : DEnv Δ Γ) → DEnv (α ∷ Δ) Γ


  mutual

    ⟦_⟧_ : ∀ {α Δ Γ} → Tm Δ α → DEnv Δ Γ → D α
    ⟦ ø ⟧ (u ∷ ρ) = u
    ⟦ t ∙ t′ ⟧ ρ = (⟦ t ⟧ ρ) (⟦ t′ ⟧ ρ)
    ⟦ ƛ t ⟧ ρ = λ u → ⟦ t ⟧ (u ∷ ρ)
    ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

    ⟦_⟧*_ : ∀ {Σ Δ Γ} → Σ ⇉ Δ → DEnv Δ Γ → DEnv Σ Γ
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
-- η-long β-normal forms.
--

data Nf : Ctx → Ty → Set where
  lam : ∀ {α β Γ} (u : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)
  ne  : ∀ {Γ} (n : Ne Nf Γ ⋆) → Nf Γ ⋆

--
-- Weakening
--

mutual

  wk-ne : ∀ {α β Γ} (n : Ne Val Γ β) → Ne Val (α ∷ Γ) β
  wk-ne (var x) = var (vs x)
  wk-ne (app n u) = app (wk-ne n) (wk-val u)

  wk-val : ∀ {α β Γ} (u : Val Γ β) → Val (α ∷ Γ) β
  wk-val (lam t ρ) = lam t (wk-env ρ)
  wk-val (ne n) = ne (wk-ne n)

  wk-env : ∀ {α Δ Γ} (ρ : Env Δ Γ) → Env Δ (α ∷ Γ)
  wk-env [] = []
  wk-env (u ∷ ρ) = wk-val u ∷ wk-env ρ


-- We can iterate weakenings using contexts.

wk-ne* : ∀ {α} Δ {Γ} (n : Ne Val Γ α) → Ne Val (Δ ++ Γ) α
wk-ne* [] n = n
wk-ne* (α ∷ Δ) n = wk-ne (wk-ne* Δ n)

wk-val* : ∀ {α} Δ {Γ} (u : Val Γ α) → Val (Δ ++ Γ) α
wk-val* [] u = u
wk-val* (α ∷ Δ) u = wk-val (wk-val* Δ u)

wk-env* : ∀ {Δ} Σ {Γ} (ρ : Env Δ Γ) → Env Δ (Σ ++ Γ)
wk-env* [] ρ = ρ
wk-env* (α ∷ Σ) ρ = wk-env (wk-env* Σ ρ)

--
-- Embedding of values and normal forms into terms.
--

var⌈_⌉ : ∀ {α Γ} (x : Var Γ α) → Tm Γ α
var⌈ vz ⌉ = ø
var⌈ vs x ⌉ = var⌈ x ⌉ [ ↑ ]

[]⇉ : ∀ {Γ} → [] ⇉ Γ
[]⇉ {[]} = ı
[]⇉ {α ∷ Γ} = []⇉ ⊙ ↑

mutual

  ne-val⌈_⌉ : ∀ {α Γ} (n : Ne Val Γ α) → Tm Γ α
  ne-val⌈ var x ⌉ = var⌈ x ⌉
  ne-val⌈ app n u ⌉ = ne-val⌈ n ⌉ ∙ val⌈ u ⌉

  val⌈_⌉ : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  val⌈ lam t ρ ⌉ =
    ƛ t [ ø ∷ (env⌈ ρ ⌉ ⊙ ↑) ]
  val⌈ ne n ⌉ = ne-val⌈ n ⌉

  env⌈_⌉ : ∀ {Δ Γ} (ρ : Env Δ Γ) → Δ ⇉ Γ
  env⌈ [] ⌉ = []⇉
  env⌈ u ∷ ρ ⌉ = val⌈ u ⌉ ∷ env⌈ ρ ⌉

mutual

  ne-nf⌈_⌉ : ∀ {α Γ} (n : Ne Nf Γ α) → Tm Γ α
  ne-nf⌈ var x ⌉ = var⌈ x ⌉
  ne-nf⌈ app n u ⌉ = ne-nf⌈ n ⌉ ∙ nf⌈ u ⌉

  nf⌈_⌉ : ∀ {α Γ} (u : Nf Γ α) → Tm Γ α
  nf⌈ lam u ⌉ = ƛ nf⌈ u ⌉
  nf⌈ ne n ⌉ = ne-nf⌈ n ⌉

-- Identity environments.

id-env : ∀ {Γ} → Env Γ Γ
id-env {[]} = []
id-env {α ∷ Γ} = ne (var vz) ∷ wk-env id-env

-- Quote.

module NaiveQuote where

  open NaiveNorm

  {-# TERMINATING #-}
  mutual

    q-val : ∀ {α Γ} (u : Val Γ α) → Nf Γ α
    q-val {⋆} (ne n) = ne (q-ne n)
    q-val {α ⇒ β} {Γ} f =
      lam {α} (q-val {β} (wk-val f ⟨∙⟩ ne (var vz)))

    q-ne : ∀ {α Γ} (n : Ne Val Γ α) → Ne Nf Γ α
    q-ne (var x) = var x
    q-ne (app n u) = app (q-ne n) (q-val u)

  norm : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
  norm t = q-val (⟦ t ⟧ id-env)

  norm-III : norm III ≡ lam (ne (var vz))
  norm-III = refl

  norm-SKK : norm (SKK {⋆}) ≡ lam (ne (var vz))
  norm-SKK = refl

  norm-SKK∙I : norm (SKK ∙ I {⋆}) ≡ lam (ne (var vz))
  norm-SKK∙I = refl

--
-- Relational big-step semantics.
--

mutual

  infix 4 ⟦_⟧_⇓_ ⟦_⟧*_⇓_ _⟨∙⟩_⇓_

  data ⟦_⟧_⇓_ : ∀ {α Δ Γ} → Tm Δ α → Env Δ Γ → Val Γ α → Set where
    ø⇓ : ∀ {α Δ Γ} {u : Val Γ α} {ρ : Env Δ Γ} →
      ⟦ ø ⟧ (u ∷ ρ) ⇓ u
    ∙⇓ : ∀ {α β Δ Γ} {t : Tm Δ (α ⇒ β)} {t′ : Tm Δ α} {ρ : Env Δ Γ} {u v w}
      (p : ⟦ t ⟧ ρ ⇓ u) (q : ⟦ t′ ⟧ ρ ⇓ v) (r : u ⟨∙⟩ v ⇓ w) →
      ⟦ t ∙ t′ ⟧ ρ ⇓ w
    ƛ⇓ : ∀ {α β Δ Γ} {t : Tm (α ∷ Δ) β} {ρ : Env Δ Γ} →
      ⟦ ƛ t ⟧ ρ ⇓ lam t ρ
    []⇓ : ∀ {α Σ Δ Γ} {t : Tm Σ α } {σ : Σ ⇉ Δ} {ρ : Env Δ Γ} {ρ′ u}
      (p : ⟦ σ ⟧* ρ ⇓ ρ′) (q : ⟦ t ⟧ ρ′ ⇓ u) →
      ⟦ t [ σ ] ⟧ ρ ⇓ u


  data ⟦_⟧*_⇓_ : ∀ {Σ Δ Γ} → Σ ⇉ Δ → Env Δ Γ → Env Σ Γ → Set where
    ι⇓ : ∀ {Γ} {ρ : Env Γ Γ} →
      ⟦ ı ⟧* ρ ⇓ ρ
    ⊙⇓ : ∀ {Σ Δ Δ′ Γ} {σ : Σ ⇉ Δ′} {σ′ : Δ′ ⇉ Δ} {ρ : Env Δ Γ} {ρ′ ρ′′}
      (p : ⟦ σ′ ⟧* ρ ⇓ ρ′) (q : ⟦ σ ⟧* ρ′ ⇓ ρ′′) →
      ⟦ σ ⊙ σ′ ⟧* ρ ⇓ ρ′′
    ∷⇓ : ∀ {α Σ Δ Γ} {t : Tm Δ α} {σ : Σ ⇉ Δ} {ρ : Env Δ Γ} {u ρ′}
      (p : ⟦ t ⟧ ρ ⇓ u) (q : ⟦ σ ⟧* ρ ⇓ ρ′) →
      ⟦ t ∷ σ ⟧* ρ ⇓ u ∷ ρ′
    ↑⇓ : ∀ {α Δ Γ} {u : Val Γ α} {ρ : Env Δ Γ} →
      ⟦ ↑ ⟧* (u ∷ ρ) ⇓ ρ

  data _⟨∙⟩_⇓_ : ∀ {α β Γ} → Val Γ (α ⇒ β) → Val Γ α → Val Γ β → Set where
    lam⇓ : ∀ {α β Δ Γ} {t : Tm (α ∷ Δ) β} {ρ : Env Δ Γ} {u v}
      (p : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v
    ne⇓  : ∀ {α β Γ} {n : Ne Val Γ (α ⇒ β)} {u} →
      ne n ⟨∙⟩ u ⇓ ne (app n u)

mutual

  data QVal_⇓_ : ∀ {α Γ} → Val Γ α → Nf Γ α → Set where
    ⋆⇓ : ∀ {Γ} (n : Ne Val Γ ⋆) {n′}
      (p : QNe n ⇓ n′) →
      QVal (ne n) ⇓ ne n′
    ⇒⇓ : ∀ {α β Γ} {f : Val Γ (α ⇒ β)} {u u′} →
      (p : wk-val f ⟨∙⟩ ne (var vz) ⇓ u) (q : QVal u ⇓ u′) →
      QVal f ⇓ lam u′

  data QNe_⇓_ : ∀ {α Γ} → Ne Val Γ α → Ne Nf Γ α → Set where
    var⇓ : ∀ {α Γ} {x : Var (α ∷ Γ) α} →
      QNe var x ⇓ var x
    app⇓ : ∀ {α β Γ} {n : Ne Val Γ (α ⇒ β)} {u : Val Γ α} {n′ u′}
      (p : QNe n ⇓ n′) (q : QVal u ⇓ u′) →
      QNe app n u ⇓ app n′ u′


data Norm_⇓_ : ∀ {α Γ} → Tm Γ α → Nf Γ α → Set where
  norm⇓ : ∀ {α Γ} {t : Tm Γ α} {u n}
    (p : ⟦ t ⟧ id-env ⇓ u) (q : QVal u ⇓ n) →
    Norm t ⇓ n

norm-III⇓ : Norm III ⇓ lam (ne (var vz))
norm-III⇓ = norm⇓ (∙⇓ ƛ⇓ (∙⇓ ƛ⇓ ƛ⇓ (lam⇓ ø⇓)) (lam⇓ ø⇓))
                   (⇒⇓ (lam⇓ ø⇓) (⋆⇓ (var vz) var⇓))
