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

open import Data.List as List
  hiding ([_])
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Properties
  using ()
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

open import Algebra
  using (module Monoid)
private
  module LM {a} {A : Set a} = Monoid (List.monoid A)


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
  vs : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

data Ne (T : Ctx → Ty → Set) : Ctx → Ty → Set where
  var : ∀ {α Γ} (x : Var Γ α) → Ne T Γ α
  app : ∀ {α β Γ} (f : Ne T Γ (α ⇒ β)) (u : T Γ α) → Ne T Γ β


mutual

  data Val : Ctx → Ty → Set where
    ne  : ∀ {α Γ} (n : Ne Val Γ α) → Val Γ α
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → Val Γ (α ⇒ β)

  data Env (Γ : Ctx) : Ctx → Set where
    []  : Env Γ []
    _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)

module NaiveNorm where

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

    _⟨∙⟩_ : ∀ {α β Γ} → Val Γ (α ⇒ β) → Val Γ α → Val Γ β
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
-- η-long β-normal forms.
--

data Nf (Γ : Ctx) : Ty → Set where
  ne  : ∀ (n : Ne Nf Γ ⋆) → Nf Γ ⋆
  lam : ∀ {α β} (m : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)

--
-- Weakening
--

mutual

  wk-ne : ∀ {α β Γ} (n : Ne Val Γ α) → Ne Val (β ∷ Γ) α
  wk-ne (var x) = var (vs x)
  wk-ne (app n u) = app (wk-ne n) (wk-val u)

  wk-val : ∀ {α β Γ} (u : Val Γ α) → Val (β ∷ Γ) α
  wk-val (lam t ρ) = lam t (wk-env ρ)
  wk-val (ne n) = ne (wk-ne n)

  wk-env : ∀ {α Γ Δ} (ρ : Env Γ Δ) → Env (α ∷ Γ) Δ
  wk-env [] = []
  wk-env (u ∷ ρ) = wk-val u ∷ wk-env ρ


-- We can iterate weakenings using contexts.

wk-ne* : ∀ {α} Δ {Γ} (n : Ne Val Γ α) → Ne Val (Δ ++ Γ) α
wk-ne* [] n = n
wk-ne* (α ∷ Δ) n = wk-ne (wk-ne* Δ n)

wk-val* : ∀ {α} Δ {Γ} (u : Val Γ α) → Val (Δ ++ Γ) α
wk-val* [] u = u
wk-val* (α ∷ Δ) u = wk-val (wk-val* Δ u)

wk-env* : ∀ {Δ} Σ {Γ} (ρ : Env Γ Δ) → Env (Σ ++ Γ) Δ
wk-env* [] ρ = ρ
wk-env* (α ∷ Σ) ρ = wk-env (wk-env* Σ ρ)

--
-- Embedding of values and normal forms into terms.
--

var⌈_⌉ : ∀ {α Γ} (x : Var Γ α) → Tm Γ α
var⌈ vz ⌉ = ø
var⌈ vs x ⌉ = var⌈ x ⌉ [ ↑ ]

sub-from-[] : ∀ {Γ} → Sub Γ []
sub-from-[] {[]} = ı
sub-from-[] {α ∷ Γ} = sub-from-[] ⊙ ↑

mutual

  ne-val⌈_⌉ : ∀ {α Γ} (n : Ne Val Γ α) → Tm Γ α
  ne-val⌈ var x ⌉ = var⌈ x ⌉
  ne-val⌈ app n u ⌉ = ne-val⌈ n ⌉ ∙ val⌈ u ⌉

  val⌈_⌉ : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  val⌈ lam t ρ ⌉ =
    ƛ t [ ø ∷ (env⌈ ρ ⌉ ⊙ ↑) ]
  val⌈ ne n ⌉ = ne-val⌈ n ⌉

  env⌈_⌉ : ∀ {Γ Δ} (ρ : Env Γ Δ) → Sub Γ Δ
  env⌈ [] ⌉ = sub-from-[]
  env⌈ u ∷ ρ ⌉ = val⌈ u ⌉ ∷ env⌈ ρ ⌉

mutual

  ne-nf⌈_⌉ : ∀ {α Γ} (n : Ne Nf Γ α) → Tm Γ α
  ne-nf⌈ var x ⌉ = var⌈ x ⌉
  ne-nf⌈ app n u ⌉ = ne-nf⌈ n ⌉ ∙ nf⌈ u ⌉

  nf⌈_⌉ : ∀ {α Γ} (m : Nf Γ α) → Tm Γ α
  nf⌈ lam m ⌉ = ƛ nf⌈ m ⌉
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
    q-val {α ⇒ β} f =
      lam (q-val (wk-val f ⟨∙⟩ ne (var vz)))

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

  data ⟦_⟧_⇓_ : ∀ {α Γ Δ} → Tm Δ α → Env Γ Δ → Val Γ α → Set where
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


  data ⟦_⟧*_⇓_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Env Γ Δ → Env Γ Σ → Set where
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

  data _⟨∙⟩_⇓_ : ∀ {α β Γ} → Val Γ (α ⇒ β) → Val Γ α → Val Γ β → Set where
    ne⇓  : ∀ {α β Γ} {n : Ne Val Γ (α ⇒ β)} {u} →
      ne n ⟨∙⟩ u ⇓ ne (app n u)
    lam⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} {u v}
      (p : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v

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


module StrongComputability-Bad where

  --
  -- "Strong computability". (A failed attempt.)
  --

  SCV : ∀ {α Γ} (u : Val Γ α) → Set
  SCV {⋆} u = ⊤
  SCV {α ⇒ β} u = ∀ v → SCV v → ∃ λ w → u ⟨∙⟩ v ⇓ w × SCV w

  SCE : ∀ {Γ Δ} (ρ : Env Γ Δ) → Set
  SCE [] = ⊤
  SCE (u ∷ ρ) = SCV u × SCE ρ

  SCS : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : Env Γ Δ) → Set
  SCS σ ρ = ∃ λ ρ′ → ⟦ σ ⟧* ρ ⇓ ρ′ × SCE ρ′

  SC : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) → Set
  SC t ρ = ∃ λ u → ⟦ t ⟧ ρ ⇓ u × SCV u

  --
  -- All values are strongly computable!
  --    ∀ {α} (u : Nf α) → SCV u
  --

  {-# TERMINATING #-}
  mutual

    -- (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → SCV (lam t ρ)

    all-scv-lam : ∀ {α β Γ Δ} (t : Tm (β ∷ Δ) α) (ρ : Env Γ Δ) → SCV (lam t ρ)
    all-scv-lam t ρ u p =
      let v , v⇓ , q = all-sc t (u ∷ ρ)
      in v , lam⇓ v⇓ , q

    -- (n : Ne Val Γ α) → SCV (ne n)

    all-scv-ne : ∀ {α Γ} (n : Ne Val Γ α) → SCV (ne n)
    all-scv-ne {⋆} n = tt
    all-scv-ne {α ⇒ β} n u p =
      ne (app n u) , ne⇓ , all-scv-ne {β} (app n u)

    -- (u : Val Γ α) → SCV u

    all-scv : ∀ {α Γ} (u : Val Γ α) → SCV u
    all-scv (lam t ρ) =
      all-scv-lam t ρ
    all-scv (ne n) =
      all-scv-ne n

    -- (ρ : Env Γ Δ) → SCE ρ

    all-sce : ∀ {Γ Δ} (ρ : Env Γ Δ) → SCE ρ
    all-sce [] = tt
    all-sce (u ∷ ρ) = all-scv u , all-sce ρ

    -- (σ : Sub Δ Σ) (ρ : Env Γ Δ) → SCS σ ρ

    all-scs : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : Env Γ Δ) → SCS σ ρ
    all-scs ı ρ =
      ρ , ι⇓ , all-sce ρ
    all-scs (σ ⊙ σ′) ρ =
      let ρ′ , ⇓ρ′ , p = all-scs σ′ ρ
          ρ′′ , ⇓ρ′′ , q = all-scs σ ρ′
      in ρ′′ , ⊙⇓ ⇓ρ′ ⇓ρ′′ , q
    all-scs (t ∷ σ) ρ =
      let
        u , u⇓ , p = all-sc t ρ
        ρ′ , ρ′⇓ , q = all-scs σ ρ
      in u ∷ ρ′ , ∷⇓ u⇓ ρ′⇓ , p , q
    all-scs ↑ (u ∷ ρ) =
      ρ , ↑⇓ , all-sce ρ

    -- ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) → SC t ρ

    all-sc : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) → SC t ρ
    all-sc ø (u ∷ ρ) =
      u , ø⇓ , all-scv u
    all-sc (t ∙ t′) ρ =
      let
        u , u⇓ , p = all-sc t ρ
        v , v⇓ , q = all-sc t′ ρ
        -- ***This call doesn't pass the termination check.***
        w , w⇓ , r = all-scv u v q
      in w , ∙⇓ u⇓ v⇓ w⇓ , r
    all-sc (ƛ t) ρ =
      lam t ρ , ƛ⇓ , all-scv-lam t ρ
    all-sc (t [ σ ]) ρ =
       let
         ρ′ , ⇓ρ′ , p = all-scs σ ρ
         u , ⇓u , q = all-sc t ρ′
       in u , []⇓ ⇓ρ′ ⇓u , q

--
-- Convertibility.
--

infix 4 _≃_

data _≃_  : ∀ {α Γ} (x y : Tm Γ α) → Set where
  ≃refl  : ∀ {α Γ} {x : Tm Γ α} →
             x ≃ x
  ≃sym   : ∀ {α Γ} {x y : Tm Γ α} →
             x ≃ y → y ≃ x
  ≃trans : ∀ {α Γ} {x y z : Tm Γ α} →
             x ≃ y → y ≃ z → x ≃ z
  ≃η     : ∀ {α β Γ} {x : Tm Γ (α ⇒ β)} →
             x ≃ (ƛ (x [ ↑ ] ∙ ø))
  ƛ-cong : ∀ {α β Γ} {x y : Tm (α ∷ Γ) β} →
             x ≃ y → (ƛ x) ≃ (ƛ y)


--
-- "Strong computability". (A failed attempt.)
--

SCV : ∀ {α Γ} (u : Val Γ α) → Set
SCV {⋆} (ne n) = ∃ λ m →
  QNe n ⇓ m
  × ne-val⌈ n ⌉ ≃ ne-nf⌈ m ⌉ 
SCV {α ⇒ β} {Γ} u = ∀ Δ v → SCV v →
  ∃ λ w → wk-val* Δ u ⟨∙⟩ v ⇓ w
    × val⌈ wk-val* Δ u ⌉ ∙ val⌈ v ⌉ ≃ val⌈ w ⌉
    × SCV w

SCE : ∀ {Γ Δ} (ρ : Env Γ Δ) → Set
SCE [] = ⊤
SCE (u ∷ ρ) = SCV u × SCE ρ

infix 6 _/∷/_
infix 5 _/Val/_

-- A shortcut for `cong (_∷_ α) Γ₁≡Γ₂`.

_/∷/_ : {Γ₁ Γ₂ : Ctx} (α : Ty) (p : Γ₁ ≡ Γ₂) →
  _≡_ {A = Ctx} (α ∷ Γ₁) (α ∷ Γ₂)
α /∷/ refl = refl

-- A shortcut for `subst (flip Val α) Γ₁≡Γ₂ u`.

_/Val/_ : ∀ {Γ₁ Γ₂ α} → Γ₁ ≡ Γ₂ → Val Γ₁ α → Val Γ₂ α
refl /Val/ u = u

/Val/∘wk-val : ∀ {Γ₁ Γ₂ α τ} (p : Γ₁ ≡ Γ₂) (u : Val Γ₁ τ) →
  (α /∷/ p) /Val/ wk-val u ≡ wk-val (p /Val/ u)
/Val/∘wk-val refl v = refl

/∷/≡cong : ∀ {Γ₁ Γ₂} α (p : Γ₁ ≡ Γ₂) → α /∷/ p ≡ cong (_∷_ α) p
/∷/≡cong α refl = refl

wk-env*[] : ∀ Σ {Γ} → wk-env* Σ {Γ} [] ≡ []
wk-env*[] [] = refl
wk-env*[] (γ ∷ Σ) =
  cong wk-env (wk-env*[] Σ)

wk-env*∷ : ∀ {α Δ} Σ {Γ} (u : Val Γ α) (ρ : Env Γ Δ) →
  wk-env* Σ (u ∷ ρ) ≡ wk-val* Σ u ∷ wk-env* Σ ρ
wk-env*∷ [] u ρ = refl
wk-env*∷ (γ ∷ Σ) u ρ rewrite wk-env*∷ Σ u ρ = refl

wk-val*++ : ∀ {α} Δ Γ Σ u →
  wk-val* Δ (wk-val* Γ u) ≡
    LM.assoc Δ Γ Σ /Val/ wk-val* {α} (Δ ++ Γ) {Σ} u
wk-val*++ [] Γ Σ u = refl
wk-val*++ {α} (γ ∷ Δ) Γ Σ u rewrite wk-val*++ Δ Γ Σ u = begin
  wk-val (LM.assoc Δ Γ Σ /Val/ wk-val* (Δ ++ Γ) u)
    ≡⟨ sym $ /Val/∘wk-val (LM.assoc Δ Γ Σ) (wk-val* (Δ ++ Γ) u) ⟩
  (γ /∷/ LM.assoc Δ Γ Σ) /Val/ wk-val (wk-val* (Δ ++ Γ) u)
    ≡⟨ cong₂ _/Val/_ (/∷/≡cong γ (LM.assoc Δ Γ Σ)) refl ⟩
  cong (_∷_ γ) (LM.assoc Δ Γ Σ) /Val/ wk-val (wk-val* (Δ ++ Γ) u)
  ∎
  where open ≡-Reasoning


mutual

  postulate
    wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wk-val* Δ u)
  {-
  wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wk-val* Δ u)
  wk-scv {⋆} u p Δ = tt
  --wk-scv {α ⇒ β} {Γ} u p Δ Σ v q = {!!}
  wk-scv {α ⇒ β} {Γ} u p Δ Σ v q =
    --p {!!} v q
    let v′ : Val ((Σ ++ Δ) ++ Γ) α
        v′ = (sym $ LM.assoc Σ Δ Γ) /Val/ v
        q′ : SCV {α} {(Σ ++ Δ) ++ Γ} v′
        q′ = subst (λ z → SCV {α} {z} {!!}) (sym $ LM.assoc Σ Δ Γ) q
        --q′ = subst (λ z → SCV {α} {{!!}} {!v′!}) (sym $ LM.assoc Σ Δ Γ) q
        r : ∃ λ w → wk-val* {!Σ ++ Δ!} u ⟨∙⟩ v ⇓ w × SCV w
        r = p {!Σ ++ Δ!} v′ q′
        s : SCV (wk-val* (Σ ++ Δ) ((sym $ LM.assoc Σ Δ Γ) /Val/ v))
        s = wk-scv {α} {(Σ ++ Δ) ++ Γ} v′ q′ (Σ ++ Δ)
    in {!!}
  -}

  {-
  wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wk-val* Δ u)
  wk-scv {⋆} {Γ} (ne n) p Δ = {!!}
  wk-scv {α ⇒ β} {Γ} u p Δ Σ v q = {!!}
  wk-scv u p [] = p
  wk-scv u p (γ ∷ Δ) = {!!}
  -}

  wk-sce : ∀ {Γ Δ} (ρ : Env Γ Δ) → SCE ρ → ∀ Σ → SCE (wk-env* Σ ρ)
  wk-sce ρ p [] = p
  wk-sce {Γ} {[]} [] p (γ ∷ Σ) rewrite wk-env*[] Σ {Γ} = tt
  wk-sce  {Γ} {α ∷ Δ} (u ∷ ρ) (p , q) (γ ∷ Σ) rewrite wk-env*∷ Σ u ρ =
    wk-scv u p (γ ∷ Σ) , wk-sce ρ q (γ ∷ Σ)


val⌈⌉∘[↑] : ∀ {α β γ Γ} (u : Val Γ (α ⇒ β)) →
  val⌈ u ⌉ [ ↑ {γ} ] ≃ val⌈ wk-val u ⌉
val⌈⌉∘[↑] (lam t ρ) = {!ƛ-cong!}
val⌈⌉∘[↑] (ne n) = {!!}

mutual

  scv→⌈⌉ : ∀ {α Γ} (u : Val Γ α) → SCV u →
    ∃ λ m → QVal u ⇓ m × val⌈ u ⌉ ≃ nf⌈ m ⌉
  scv→⌈⌉ {⋆} (ne n) (m , ⇓m , n≃m) =
    ne m , ⋆⇓ n ⇓m , n≃m
  scv→⌈⌉ {α ⇒ β} {Γ} u p =
    let
      r : SCV {α} {α ∷ Γ} (ne (var vz))
      r = ⌈⌉→scv (var vz) (var vz) var⇓ ≃refl
      pvzr : ∃ λ v → wk-val u ⟨∙⟩ ne (var vz) ⇓ v
        × val⌈ wk-val u ⌉ ∙ ø ≃ val⌈ v ⌉
        × SCV {β} {α ∷ Γ} v
      pvzr = p (α ∷ []) (ne (var vz)) r
      v , ⇓v , ≃⌈v⌉ , q = pvzr
      vq : ∃ λ m → QVal v ⇓ m × val⌈ v ⌉ ≃ nf⌈ m ⌉
      vq = scv→⌈⌉ {β} v q
      m , v⇓m , ⌈v⌉≃⌈m⌉ = vq
      ⇓lam-m : QVal u ⇓ lam m
      ⇓lam-m = ⇒⇓ ⇓v v⇓m
      xxx : val⌈ wk-val u ⌉ ∙ ø ≃ nf⌈ m ⌉
      xxx = ≃trans ≃⌈v⌉ ⌈v⌉≃⌈m⌉
    in lam m , ⇓lam-m
           , (val⌈ u ⌉ ≃ nf⌈ lam m ⌉ ∋ {!!})
             --≃trans (≃sym {!cong val⌈_⌉!}) {!!}
{-
val⌈ u ⌉ ≃ ƛ val⌈ u ⌉ [ ↑ ] ∙ ø ≃
ƛ val⌈ wk-val u ⌉ ∙ ø ≃
ƛ val⌈ v ⌉ ≃ ƛ nf⌈ m ⌉ ≃ nf⌈ lam m ⌉

val⌈ u ⌉ [ ↑ ] ≃ val⌈ wk-val u ⌉
-}

  ⌈⌉→scv : ∀ {α Γ} (n : Ne Val Γ α) (m : Ne Nf Γ α) →
    QNe n ⇓ m → ne-val⌈ n ⌉ ≃ ne-nf⌈ m ⌉ → SCV (ne n)
  ⌈⌉→scv {⋆} n m ⇓m n≃m =
    m , ⇓m , n≃m
  ⌈⌉→scv {α ⇒ β} n m ⇓m n≃m Δ u p =
    {!!} , {!!}
