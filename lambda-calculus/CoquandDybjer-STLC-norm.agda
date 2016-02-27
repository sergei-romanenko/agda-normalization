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

module CoquandDybjer-STLC-norm where

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

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

Ctx : Set
Ctx = List Ty

-- We will use the associativity of _++_

module CtxMonoid = Monoid (List.monoid Ty)

--
-- Environments.
--

data Env (T : Ctx → Ty → Set) (Γ : Ctx) : Ctx → Set where
  [] : Env T Γ []
  _∷_ : ∀ {Δ α} (v : T Γ α) (ρ : Env T Γ Δ) → Env T Γ (α ∷ Δ)


--
-- Terms and substitutions.
--

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
    _⊙_ : ∀ {Γ Δ Σ} (σ : Sub Δ Γ) (σ′ : Sub Σ Δ) → Sub Σ Γ
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
-- Variables.
--

data Var : Ctx → Ty → Set where
  vz : ∀ {α Γ} → Var (α ∷ Γ) α
  vs : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

--
-- Renamings.
--

Ren : (Γ Δ : Ctx) → Set
Ren = Env Var

-- Weakening of renamings.

wkRen : ∀ {Γ Δ α} (ρ : Ren Γ Δ) → Ren (α ∷ Γ) Δ
wkRen [] = []
wkRen (x ∷ ρ) = vs x ∷ wkRen ρ 

wkRen* : ∀ {Γ Δ} Σ (ρ : Ren Γ Δ) → Ren (Σ ++ Γ) Δ
wkRen* [] ρ = ρ
wkRen* (α ∷ Σ) ρ = wkRen (wkRen* Σ ρ)

-- Identity.

idRen : ∀ {Γ} → Ren Γ Γ
idRen {[]} = []
idRen {α ∷ Γ} = vz ∷ wkRen idRen

-- Lifting of renamings.

liftRen : ∀ {α Γ Δ} → Ren Γ Δ → Ren (α ∷ Γ) (α ∷ Δ)
liftRen ρ = vz ∷ wkRen ρ

-- Applying renamings to variables.

renVar : ∀ {Γ Δ α} (x : Var Δ α) (ρ : Ren Γ Δ) → Var Γ α
renVar vz (y ∷ ρ) = y
renVar (vs x) (y ∷ ρ) = renVar x ρ

--
-- Weak head normal forms.
--

data Ne (T : Ctx → Ty → Set) : Ctx → Ty → Set where
  var : ∀ {α Γ} (x : Var Γ α) → Ne T Γ α
  app : ∀ {α β Γ} (f : Ne T Γ (α ⇒ β)) (u : T Γ α) → Ne T Γ β


module NaiveNorm where

  data Val : Ctx → Ty → Set where
    ne  : ∀ {α Γ} (n : Ne Val Γ α) → Val Γ α
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Val Γ Δ) → Val Γ (α ⇒ β)

  {-# TERMINATING #-}
  mutual

    infixl 5 _⟨∙⟩_

    ⟦_⟧_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Val Γ Δ) → Val Γ α
    ⟦ ø ⟧ (u ∷ ρ) = u
    ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
    ⟦ ƛ t ⟧ ρ = lam t ρ
    ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

    ⟦_⟧*_ : ∀ {Γ Δ Σ} (σ : Sub Γ Δ) (ρ : Env Val Σ Γ) → Env Val Σ Δ
    ⟦ ı ⟧* ρ = ρ
    ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
    ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
    ⟦ ↑ ⟧* (u ∷ ρ) = ρ

    _⟨∙⟩_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) → Val Γ β
    ne n ⟨∙⟩ v = ne (app n v)
    lam t ρ ⟨∙⟩ v = ⟦ t ⟧ (v ∷ ρ)

  ⟦III⟧ : ⟦ III ⟧ ([] {Val} {[]}) ≡ lam ø []
  ⟦III⟧ = refl

  ⟦SKK⟧ : ⟦ SKK {⋆} ⟧ ([] {Val} {[]}) ≡
    lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
        (lam (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))
  ⟦SKK⟧ = refl

  ⟦SKK∙I⟧ : ⟦ SKK ∙ I {⋆} ⟧ ([] {Val} {[]}) ≡ lam ø []
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


data Nf : Ctx → Ty → Set where
  ne  : ∀ {Γ} (n : Ne Nf Γ ⋆) → Nf Γ ⋆
  lam : ∀ {Γ α β} (m : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)

-- Structure-preserving conversion to terms.

embVar : ∀ {Γ α} (x : Var Γ α) → Tm Γ α
embVar vz = ø
embVar (vs x) = embVar x [ ↑ ]

mutual

  embNe : ∀ {Γ α} (n : Ne Nf Γ α) → Tm Γ α
  embNe (var x) = embVar x
  embNe (app n m) = embNe n ∙ embNf m

  embNf : ∀ {Γ α} (m : Nf Γ α) → Tm Γ α
  embNf (ne n) = embNe n
  embNf (lam m) = ƛ embNf m

--
-- Applying renamings to normal forms.
--

mutual

  renNe : ∀ {Γ Δ α} (n : Ne Nf Δ α) (ρ : Ren Γ Δ) → Ne Nf Γ α
  renNe (var x) ρ = var (renVar x ρ)
  renNe (app n u) ρ = app (renNe n ρ) (renNf u ρ)

  renNf : ∀ {Γ Δ α} (m : Nf Δ α) (ρ : Ren Γ Δ) → Nf Γ α
  renNf (ne n) ρ = ne (renNe n ρ)
  renNf (lam m) ρ = lam (renNf m (liftRen ρ))

-- Weakening of Ne Nf.

wkNe* : ∀ {α Γ} Δ (n : Ne Nf Γ α) → Ne Nf (Δ ++ Γ) α
wkNe* Δ n = renNe n (wkRen* Δ idRen)

--
-- Values.
--

Val : Ctx → Ty → Set
Val Γ ⋆ = Ne Nf Γ ⋆
Val Γ (α ⇒ β) = ∀ Δ → Val (Δ ++ Γ) α → Val (Δ ++ Γ) β

-- Value environments.

VEnv : Ctx → Ctx → Set
VEnv = Env Val

-- Weakening of values.

wkVal* : ∀ {α Γ} Δ (u : Val Γ α) → Val (Δ ++ Γ) α
wkVal* {⋆} Δ n = wkNe* Δ n
wkVal* {α ⇒ β} {Γ} Δ f = λ Δ′ v →
  let
    ⟨_⟩₁ : Val (Δ′ ++ Δ ++ Γ) α → Val ((Δ′ ++ Δ) ++ Γ) α
    ⟨_⟩₁ = subst (flip Val α) (sym $ CtxMonoid.assoc Δ′ Δ Γ)
    ⟨_⟩₂ : Val ((Δ′ ++ Δ) ++ Γ) β → Val (Δ′ ++ Δ ++ Γ) β
    ⟨_⟩₂ = subst (flip Val β) (CtxMonoid.assoc Δ′ Δ Γ)
  in ⟨ f (Δ′ ++ Δ) ⟨ v ⟩₁ ⟩₂

wkVal : ∀ {γ α Γ} (u : Val Γ α) → Val (γ ∷ Γ) α
wkVal {γ} u = wkVal* (γ ∷ []) u

-- Weakening of value environments.

wkVEnv* : ∀ {Γ Δ} Σ (ρ : VEnv Γ Δ) → VEnv (Σ ++ Γ) Δ
wkVEnv* Σ [] = []
wkVEnv* {Γ} {α ∷ Δ} Σ (u ∷ ρ) = wkVal* Σ u ∷ wkVEnv* Σ ρ

wkVEnv : ∀ {γ Γ Δ} (ρ : VEnv Γ Δ) → VEnv (γ ∷ Γ) Δ
wkVEnv {γ} ρ = wkVEnv* (γ ∷ []) ρ

--
-- Evaluation: terms to values.
--

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {Γ α β} (t : Val Γ (α ⇒ β)) (t′ : Val Γ α) → Val Γ β
t ⟨∙⟩ t′ = t [] t′

mutual

  ⟦_⟧ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : VEnv Γ Δ) → Val Γ α
  ⟦ ø ⟧ (u ∷ ρ) = u
  ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
  ⟦ ƛ t ⟧ ρ = λ Δ u → ⟦ t ⟧ (u ∷ wkVEnv* Δ ρ)
  ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

  ⟦_⟧* : ∀ {Γ Δ Σ} (σ : Sub Δ Σ) (ρ : VEnv Γ Δ) → VEnv Γ Σ
  ⟦ ı ⟧* ρ = ρ
  ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
  ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
  ⟦ ↑ ⟧* (u ∷ ρ) = ρ

--
-- Reflection and reification.
--

mutual

  reflect : ∀ {α Γ} (n : Ne Nf Γ α) → Val Γ α
  reflect {⋆} n = n
  reflect {α ⇒ β} n = λ Δ u → reflect (app (wkNe* Δ n) (reify u))

  reify : ∀ {α Γ} (u : Val Γ α) → Nf Γ α
  reify {⋆} n = ne n
  reify {α ⇒ β} f = lam (reify (f (α ∷ []) (reflect (var vz))))

--
-- Normalisation.
--

idVEnv : ∀ {Γ} → VEnv Γ Γ
idVEnv {[]} = []
idVEnv {α ∷ Γ} = reflect (var vz) ∷ wkVEnv idVEnv

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf t = reify (⟦ t ⟧ idVEnv)

⟪_⟫ : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
⟪ u ⟫ = embNf (reify u)

norm : ∀ {α Γ} (t : Tm Γ α) → Tm Γ α
norm = embNf ∘ nf

--
-- Examples.
--

norm-III : norm III ≡ (ƛ ø)
norm-III = refl

norm-SKK : norm (SKK {⋆}) ≡ (ƛ ø)
norm-SKK = refl

norm-SKK∙I : norm (SKK ∙ I {⋆})  ≡ (ƛ ø)
norm-SKK∙I = refl
