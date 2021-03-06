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
  using (Any; here; there)
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

  wkNe : ∀ {α β Γ} (n : Ne Val Γ α) → Ne Val (β ∷ Γ) α
  wkNe (var x) = var (vs x)
  wkNe (app n u) = app (wkNe n) (wkVal u)

  wkVal : ∀ {α β Γ} (u : Val Γ α) → Val (β ∷ Γ) α
  wkVal (lam t ρ) = lam t (wkEnv ρ)
  wkVal (ne n) = ne (wkNe n)

  wkEnv : ∀ {α Γ Δ} (ρ : Env Γ Δ) → Env (α ∷ Γ) Δ
  wkEnv [] = []
  wkEnv (u ∷ ρ) = wkVal u ∷ wkEnv ρ


-- We can iterate weakenings using contexts.

wkNe* : ∀ {α} Δ {Γ} (n : Ne Val Γ α) → Ne Val (Δ ++ Γ) α
wkNe* [] n = n
wkNe* (α ∷ Δ) n = wkNe (wkNe* Δ n)

wkVal* : ∀ {α} Δ {Γ} (u : Val Γ α) → Val (Δ ++ Γ) α
wkVal* [] u = u
wkVal* (α ∷ Δ) u = wkVal (wkVal* Δ u)

wkEnv* : ∀ {Δ} Σ {Γ} (ρ : Env Γ Δ) → Env (Σ ++ Γ) Δ
wkEnv* [] ρ = ρ
wkEnv* (α ∷ Σ) ρ = wkEnv (wkEnv* Σ ρ)

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

  embNeVal : ∀ {α Γ} (n : Ne Val Γ α) → Tm Γ α
  embNeVal (var x) = embVar x
  embNeVal (app n u) = embNeVal n ∙ embVal u

  embVal : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  embVal (lam t ρ) =
    --ƛ t [ ø ∷ (embEnv ρ ⊙ ↑) ]
    (ƛ t) [ embEnv ρ ]
  embVal (ne n) = embNeVal n

  embEnv : ∀ {Γ Δ} (ρ : Env Γ Δ) → Sub Γ Δ
  embEnv [] = sub-from-[]
  embEnv (u ∷ ρ) = embVal u ∷ embEnv ρ

mutual

  embNeNf : ∀ {α Γ} (n : Ne Nf Γ α) → Tm Γ α
  embNeNf (var x) = embVar x
  embNeNf (app n u) = embNeNf n ∙ embNf u

  embNf : ∀ {α Γ} (m : Nf Γ α) → Tm Γ α
  embNf (lam m) = ƛ embNf m
  embNf (ne n) = embNeNf n

-- Identity environments.

id-env : ∀ {Γ} → Env Γ Γ
id-env {[]} = []
id-env {α ∷ Γ} = ne (var vz) ∷ wkEnv id-env

-- Quote.

module NaiveQuote where

  open NaiveNorm

  {-# TERMINATING #-}
  mutual

    q-val : ∀ {α Γ} (u : Val Γ α) → Nf Γ α
    q-val {⋆} (ne n) = ne (q-ne n)
    q-val {α ⇒ β} f =
      lam (q-val (wkVal f ⟨∙⟩ ne (var vz)))

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
      (p : wkVal f ⟨∙⟩ ne (var vz) ⇓ u) (q : QVal u ⇓ u′) →
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

infix 4 _≈_ _≃_

mutual

  -- σ₁ ≃ σ₂

  data _≃_ : ∀ {Γ Δ} (σ₁ σ₂ : Sub Γ Δ) → Set where
    ≃refl  : ∀ {Γ Δ} {σ : Sub Γ Δ} →
               σ ≃ σ
    ≃sym   : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} →
               σ₁ ≃ σ₂ → σ₂ ≃ σ₁
    ≃trans : ∀ {Γ Δ} {σ₁ σ₂ σ₃ : Sub Γ Δ} →
               σ₁ ≃ σ₂ → σ₂ ≃ σ₃ → σ₁ ≃ σ₃
    ≃⊙-cong  : ∀ {Γ Δ Σ} {σ₁ σ₂ : Sub Δ Γ} {τ₁ τ₂ : Sub Σ Δ} →
                 σ₁ ≃ σ₂ → τ₁ ≃ τ₂ → σ₁ ⊙ τ₁ ≃ σ₂ ⊙ τ₂
    ≃∷-cong  : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α} {σ₁ σ₂ : Sub Δ Γ} →
                 t₁ ≈ t₂ → σ₁ ≃ σ₂ → t₁ ∷ σ₁ ≃ t₂ ∷ σ₂
    ≃assoc : ∀ {Γ Δ Δ′ Σ} {σ₁ : Sub Δ Γ} {σ₂ : Sub Δ′ Δ} {σ₃ : Sub Σ Δ′} →
               (σ₁ ⊙ σ₂) ⊙ σ₃ ≃ σ₁ ⊙ (σ₂ ⊙ σ₃)
    ≃idl   : ∀ {Γ Δ} {σ : Sub Γ Δ} →
               ı ⊙ σ ≃ σ
    ≃idr   : ∀ {Γ Δ} {σ : Sub Γ Δ} →
               σ ⊙ ı ≃ σ
    ≃wk    : ∀ {α Γ Δ} {σ : Sub Γ Δ} {t : Tm Γ α} →
               ↑ ⊙ (t ∷ σ) ≃ σ
    ≃cons  : ∀ {α Γ Δ Σ} {σ : Sub Δ Γ} {t : Tm Δ α} {σ′ : Sub Σ Δ} →
               (t ∷ σ) ⊙ σ′ ≃ t [ σ′ ] ∷ (σ ⊙ σ′)
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
               (t₁ ∙ t₂) [ σ ] ≈ t₁ [ σ ] ∙ t₂ [ σ ]
    ≈βσ    : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) (α ⇒ β)} {σ : Sub Γ Δ} {t′ : Tm Γ α} →
               (ƛ t) [ σ ] ∙ t′ ≈ t [ t′ ∷ σ ]
    ≈η     : ∀ {α β Γ} {t : Tm Γ (α ⇒ β)} →
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
-- "Strong computability". (A failed attempt.)
--

SCV : ∀ {α Γ} (u : Val Γ α) → Set
SCV {⋆} (ne n) = ∃ λ m →
  QNe n ⇓ m
  × embNeVal n ≈ embNeNf m
SCV {α ⇒ β} {Γ} u = ∀ Δ v → SCV v →
  ∃ λ w → wkVal* Δ u ⟨∙⟩ v ⇓ w
    × embVal (wkVal* Δ u) ∙ embVal v ≈ embVal w
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

/Val/∘wkVal : ∀ {Γ₁ Γ₂ α τ} (p : Γ₁ ≡ Γ₂) (u : Val Γ₁ τ) →
  (α /∷/ p) /Val/ wkVal u ≡ wkVal (p /Val/ u)
/Val/∘wkVal refl v = refl

/∷/≡cong : ∀ {Γ₁ Γ₂} α (p : Γ₁ ≡ Γ₂) → α /∷/ p ≡ cong (_∷_ α) p
/∷/≡cong α refl = refl

wkEnv*[] : ∀ Σ {Γ} → wkEnv* Σ {Γ} [] ≡ []
wkEnv*[] [] = refl
wkEnv*[] (γ ∷ Σ) =
  cong wkEnv (wkEnv*[] Σ)

wkEnv*∷ : ∀ {α Δ} Σ {Γ} (u : Val Γ α) (ρ : Env Γ Δ) →
  wkEnv* Σ (u ∷ ρ) ≡ wkVal* Σ u ∷ wkEnv* Σ ρ
wkEnv*∷ [] u ρ = refl
wkEnv*∷ (γ ∷ Σ) u ρ rewrite wkEnv*∷ Σ u ρ = refl

wkVal*++ : ∀ {α} Δ Γ Σ u →
  wkVal* Δ (wkVal* Γ u) ≡
    LM.assoc Δ Γ Σ /Val/ wkVal* {α} (Δ ++ Γ) {Σ} u
wkVal*++ [] Γ Σ u = refl
wkVal*++ {α} (γ ∷ Δ) Γ Σ u rewrite wkVal*++ Δ Γ Σ u = begin
  wkVal (LM.assoc Δ Γ Σ /Val/ wkVal* (Δ ++ Γ) u)
    ≡⟨ sym $ /Val/∘wkVal (LM.assoc Δ Γ Σ) (wkVal* (Δ ++ Γ) u) ⟩
  (γ /∷/ LM.assoc Δ Γ Σ) /Val/ wkVal (wkVal* (Δ ++ Γ) u)
    ≡⟨ cong₂ _/Val/_ (/∷/≡cong γ (LM.assoc Δ Γ Σ)) refl ⟩
  cong (_∷_ γ) (LM.assoc Δ Γ Σ) /Val/ wkVal (wkVal* (Δ ++ Γ) u)
  ∎
  where open ≡-Reasoning


mutual

  postulate
    wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wkVal* Δ u)
  {-
  wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wkVal* Δ u)
  wk-scv {⋆} u p Δ = tt
  --wk-scv {α ⇒ β} {Γ} u p Δ Σ v q = {!!}
  wk-scv {α ⇒ β} {Γ} u p Δ Σ v q =
    --p {!!} v q
    let v′ : Val ((Σ ++ Δ) ++ Γ) α
        v′ = (sym $ LM.assoc Σ Δ Γ) /Val/ v
        q′ : SCV {α} {(Σ ++ Δ) ++ Γ} v′
        q′ = subst (λ z → SCV {α} {z} {!!}) (sym $ LM.assoc Σ Δ Γ) q
        --q′ = subst (λ z → SCV {α} {{!!}} {!v′!}) (sym $ LM.assoc Σ Δ Γ) q
        r : ∃ λ w → wkVal* {!Σ ++ Δ!} u ⟨∙⟩ v ⇓ w × SCV w
        r = p {!Σ ++ Δ!} v′ q′
        s : SCV (wkVal* (Σ ++ Δ) ((sym $ LM.assoc Σ Δ Γ) /Val/ v))
        s = wk-scv {α} {(Σ ++ Δ) ++ Γ} v′ q′ (Σ ++ Δ)
    in {!!}
  -}

  {-
  wk-scv : ∀ {α Γ} (u : Val Γ α) → SCV u → ∀ Δ → SCV (wkVal* Δ u)
  wk-scv {⋆} {Γ} (ne n) p Δ = {!!}
  wk-scv {α ⇒ β} {Γ} u p Δ Σ v q = {!!}
  wk-scv u p [] = p
  wk-scv u p (γ ∷ Δ) = {!!}
  -}

  wk-sce : ∀ {Γ Δ} (ρ : Env Γ Δ) → SCE ρ → ∀ Σ → SCE (wkEnv* Σ ρ)
  wk-sce ρ p [] = p
  wk-sce {Γ} {[]} [] p (γ ∷ Σ) rewrite wkEnv*[] Σ {Γ} = tt
  wk-sce  {Γ} {α ∷ Δ} (u ∷ ρ) (p , q) (γ ∷ Σ) rewrite wkEnv*∷ Σ u ρ =
    wk-scv u p (γ ∷ Σ) , wk-sce ρ q (γ ∷ Σ)

mutual

  embNeVal∘[↑] : ∀ {α γ Γ} (n : Ne Val Γ α) →
    embNeVal n [ ↑ {γ} ] ≈ embNeVal (wkNe n)
  embNeVal∘[↑] (var x) = ≈refl
  embNeVal∘[↑] (app n u) = begin
    (embNeVal n ∙ embVal u) [ ↑ ]
      ≈⟨ ≈app ⟩
    embNeVal n [ ↑ ] ∙ embVal u [ ↑ ]
      ≈⟨ ≈∙-cong (embNeVal∘[↑] n) (embVal∘[↑] u) ⟩
    embNeVal (wkNe n) ∙ embVal (wkVal u)
    ∎
    where open ≈-Reasoning

  embVal∘[↑] : ∀ {α γ Γ} (u : Val Γ α) →
    embVal u [ ↑ {γ} ] ≈ embVal (wkVal {α} u)
  embVal∘[↑] (lam t ρ) = begin
    embVal (lam t ρ) [ ↑ ]
      ≡⟨⟩
    (ƛ t) [ embEnv ρ ] [ ↑ ]
      ≈⟨ ≈sym ≈comp ⟩
    (ƛ t) [ embEnv ρ ⊙ ↑ ]
      ≈⟨ ≈[]-cong ≈refl (embEnv∘⊙↑ ρ) ⟩
    (ƛ t) [ embEnv (wkEnv ρ) ]
      ≡⟨⟩
    embVal (wkVal (lam t ρ))
    ∎
    where open ≈-Reasoning
  embVal∘[↑] (ne n) =
    embNeVal∘[↑] n

  embVal∘[↑]′ : ∀ {α β Γ Δ} (σ : Sub Γ Δ) →
    (ø ∷ σ ⊙ ↑) ⊙ (ø ∷ ↑ {α} ⊙ ↑ {β}) ≃ ø ∷ (σ ⊙ ↑) ⊙ ↑
  embVal∘[↑]′ σ = begin
    (ø ∷ σ ⊙ ↑) ⊙ (ø ∷ ↑ ⊙ ↑)
      ≈⟨ ≃cons ⟩
    ø [ ø ∷ ↑ ⊙ ↑ ] ∷ (σ ⊙ ↑) ⊙ (ø ∷ ↑ ⊙ ↑)
      ≈⟨ ≃∷-cong ≈proj ≃assoc ⟩
    ø ∷ σ ⊙ (↑ ⊙ (ø ∷ ↑ ⊙ ↑))
      ≈⟨ ≃∷-cong ≈refl (≃⊙-cong ≃refl ≃wk) ⟩
    ø ∷ σ ⊙ (↑ ⊙ ↑)
      ≈⟨ ≃∷-cong ≈refl (≃sym ≃assoc) ⟩
    ø ∷ (σ ⊙ ↑) ⊙ ↑
    ∎
    where open ≃-Reasoning

  embEnv∘⊙↑ : ∀ {γ Γ Δ} (ρ : Env Γ Δ) →
    embEnv ρ ⊙ ↑ {γ} ≃ embEnv (wkEnv ρ)
  embEnv∘⊙↑ [] = ≃refl
  embEnv∘⊙↑ (u ∷ ρ) = begin
    (embVal u ∷ embEnv ρ) ⊙ ↑
      ≈⟨ ≃cons ⟩
    embVal u [ ↑ ] ∷ embEnv ρ ⊙ ↑
      ≈⟨ ≃∷-cong (embVal∘[↑] u) (embEnv∘⊙↑ ρ) ⟩
    embVal (wkVal u) ∷ embEnv (wkEnv ρ)
    ∎
    where open ≃-Reasoning


wkVal*∘ne : ∀ {α β Γ} (n : Ne Val Γ (α ⇒ β)) Δ →
  wkVal* Δ (ne n) ≡ ne (wkNe* Δ n)
wkVal*∘ne n [] = refl
wkVal*∘ne n (γ ∷ Δ) = begin
  wkVal (wkVal* Δ (ne n))
    ≡⟨ cong wkVal (wkVal*∘ne n Δ) ⟩
  wkVal (ne (wkNe* Δ n))
    ≡⟨⟩
  ne (wkNe (wkNe* Δ n))
  ∎
  where open ≡-Reasoning

wkVal*-ne : ∀ {α β Γ} (n : Ne Val Γ (α ⇒ β)) Δ u →
  wkVal* Δ (ne n) ⟨∙⟩ u ⇓ ne (app (wkNe* Δ n) u)
wkVal*-ne n Δ u rewrite wkVal*∘ne n Δ =
  ne⇓

mutual

  scv→⌈⌉ : ∀ {α Γ} (u : Val Γ α) → SCV u →
    ∃ λ m → QVal u ⇓ m × embVal u ≈ embNf m
  scv→⌈⌉ {⋆} (ne n) (m , ⇓m , n≈m) =
    ne m , ⋆⇓ n ⇓m , n≈m
  scv→⌈⌉ {α ⇒ β} {Γ} u p =
    let
      r : SCV {α} {α ∷ Γ} (ne (var vz))
      r = ⌈⌉→scv (var vz) (var vz) var⇓ ≈refl
      pvzr : ∃ λ v → wkVal u ⟨∙⟩ ne (var vz) ⇓ v
        × embVal (wkVal u) ∙ ø ≈ embVal v
        × SCV {β} {α ∷ Γ} v
      pvzr = p (α ∷ []) (ne (var vz)) r
      v , ⇓v , ≈⌈v⌉ , q = pvzr
      vq : ∃ λ m → QVal v ⇓ m × embVal v ≈ embNf m
      vq = scv→⌈⌉ {β} v q
      m , v⇓m , ⌈v⌉≈⌈m⌉ = vq
      ⇓lam-m : QVal u ⇓ lam m
      ⇓lam-m = ⇒⇓ ⇓v v⇓m
      val≈nf : embVal u ≈ embNf (lam m)
      val≈nf = begin
        embVal u
          ≈⟨ ≈η ⟩
        ƛ embVal u [ ↑ ] ∙ ø
          ≈⟨ ≈ƛ-cong (≈∙-cong (embVal∘[↑] u) ≈refl) ⟩
        ƛ embVal (wkVal u) ∙ ø
          ≈⟨ ≈ƛ-cong ≈⌈v⌉ ⟩
        ƛ embVal v
          ≈⟨ ≈ƛ-cong ⌈v⌉≈⌈m⌉ ⟩
        ƛ embNf m
          ≡⟨⟩
        embNf (lam m)
        ∎
    in lam m , ⇓lam-m , val≈nf
    where open ≈-Reasoning

  ⌈⌉→scv : ∀ {α Γ} (n : Ne Val Γ α) (m : Ne Nf Γ α) →
    QNe n ⇓ m → embNeVal n ≈ embNeNf m → SCV (ne n)
  ⌈⌉→scv {⋆} n m ⇓m n≈m =
    m , ⇓m , n≈m
  ⌈⌉→scv {α ⇒ β} {Γ} n m ⇓m n≈m Δ u p =
    let
      nu : Val (Δ ++ Γ) β
      nu = ne (app (wkNe* Δ n) u)
      ⇓nu : wkVal* Δ (ne n) ⟨∙⟩ u ⇓ ne (app (wkNe* Δ n) u)
      ⇓nu = wkVal*-ne n Δ u
      n≈n : embVal (wkVal* Δ (ne n)) ≈ embNeVal (wkNe* Δ n)
      n≈n = begin
        embVal (wkVal* Δ (ne n))
          ≡⟨ cong embVal (wkVal*∘ne n Δ) ⟩
        embVal (ne (wkNe* Δ n))
          ≡⟨⟩
        embNeVal (wkNe* Δ n)
        ∎
      nu≈nu : embVal (wkVal* Δ (ne n)) ∙ embVal u ≈
              embNeVal (wkNe* Δ n) ∙ embVal u
      nu≈nu = ≈∙-cong n≈n ≈refl
      m′ , ⇓m′ , u≈m′ = ∃ (λ m′ → QVal u ⇓ m′ × embVal u ≈ embNf m′)
        ∋ scv→⌈⌉ u p
      yyy : SCV (wkVal* Δ (ne n))
      yyy = wk-scv (ne n) {!p!} Δ
      qqq : SCV {α ⇒ β} {Δ ++ Γ} (ne (wkNe* Δ n))
      qqq = subst SCV (wkVal*∘ne n Δ) yyy
      zzz : QNe app (wkNe* Δ n) u ⇓ app {!wkNe* Δ m!} m′
      zzz = app⇓ {!!} ⇓m′
      scv-nu : SCV {β} {Δ ++ Γ} (ne (app (wkNe* Δ n) u))
      scv-nu = ⌈⌉→scv {β} {Δ ++ Γ} (app (wkNe* Δ n) u) (app {!!} m′) zzz
                      (≈∙-cong {!!} u≈m′) 
    in nu , ⇓nu , nu≈nu , scv-nu
    where open ≈-Reasoning

--   wkVal* Δ (ne n) ≡ ne (wkNe* Δ n)
