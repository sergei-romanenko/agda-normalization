{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  Based on

    Thierry Coquand and Peter Dybjer. 1997.
    Intuitionistic model constructions and normalization proofs.
    Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
    DOI=10.1017/S0960129596002150 http://dx.doi.org/10.1017/S0960129596002150 

  and

    Peter Dybjer and Andrzej Filinski. 2000.
    Normalization and Partial Evaluation.
    In Applied Semantics, International Summer School, APPSEM 2000, Caminha,
    Portugal, September 9-15, 2000, Advanced Lectures,
    Gilles Barthe, Peter Dybjer, Luis Pinto, and João Saraiva (Eds.).
    Springer-Verlag, London, UK, UK, 137-192.

  and

    Andreas Abel and James Chapman. 2014.
    Normalization by evaluation in the delay monad: A case study for
    coinduction via copatterns and sized types.
    In MSFP'14, volume 153 of EPTCS, pages 51--67.
    http://arxiv.org/abs/1406.2059v1

-}

{-# OPTIONS --copatterns #-}

module STCC-Delay-SK-norm where

open import Agda.Primitive
open import Size
open import Category.Monad
  using (RawMonad; module RawMonad)

open import Data.Nat
open import Data.Empty
open import Data.Unit
  using (⊤; tt)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

--
-- Coinductive delay monad.
--

mutual

  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

module Bind where
  infixl 1 _>>=_

  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

--
-- Termination/Convergence.  Makes sense only for Delay A ∞.
--

infix 4 _⇓_

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Lifting a predicate to Delay using convergence.

record Delay⇓ {A : Set} (P : A → Set) (a? : Delay ∞ A) : Set where
  constructor delay⇓
  field
    a  : A
    a⇓ : a? ⇓ a
    pa : P a

-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A}
  (f : A → B) (⇓a : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

⇓bind : ∀ {A B} (f : A → Delay ∞ B)
  {a? : Delay ∞ A} {a : A} (⇓a : a? ⇓ a)
  {fa : B} (⇓fa : (a? >>= f) ⇓ fa) → f a ⇓ fa
⇓bind f now⇓ ⇓fa = ⇓fa
⇓bind f (later⇓ ⇓a) (later⇓ ⇓fa) = ⇓bind f ⇓a ⇓fa

⇓bind₂ : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C} (⇓fab : (a? >>= (λ a → b? >>= f a)) ⇓ fab) → f a b ⇓ fab
⇓bind₂ f now⇓ now⇓ ⇓fab = ⇓fab
⇓bind₂ f now⇓ (later⇓ ⇓b) (later⇓ ⇓fab) = ⇓bind₂ f now⇓ ⇓b ⇓fab
⇓bind₂ f (later⇓ ⇓a) ⇓b (later⇓ ⇓fab) = ⇓bind₂ f ⇓a ⇓b ⇓fab

bind⇓ : ∀ {A B} (f : A → Delay ∞ B)
  {a? a} (⇓a : a? ⇓ a) {fa} (⇓fa : f a ⇓ fa) →
  (a? >>= f) ⇓ fa
bind⇓ f now⇓ ⇓fa = ⇓fa
bind⇓ f (later⇓ ⇓a) ⇓fa = later⇓ (bind⇓ f ⇓a ⇓fa)

bind⇓₂ : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C}  (⇓fab : f a b ⇓ fab) →
  (a? >>= (λ a → b? >>= f a)) ⇓ fab
bind⇓₂ f now⇓ now⇓ ⇓fab = ⇓fab
bind⇓₂ f now⇓ (later⇓ ⇓b) ⇓fab = later⇓ (bind⇓₂ f now⇓ ⇓b ⇓fab)
bind⇓₂ f (later⇓ ⇓a) ⇓b ⇓fab = later⇓ (bind⇓₂ f ⇓a ⇓b ⇓fab)


--
-- Determinism: a? ⇓ a₁ → a? ⇓ a₂ → a₁ ≡ a₁
-- 

⇓-det : ∀ {A} {a? : Delay ∞ A}
  {a₁} (⇓a₁ : a? ⇓ a₁) {a₂} (⇓a₂ : a? ⇓ a₂) → 
  a₁ ≡ a₂
⇓-det now⇓ now⇓ = refl
⇓-det (later⇓ ⇓a₁) (later⇓ ⇓a₂) = ⇓-det ⇓a₁ ⇓a₂

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Convertibility
--

infix 4 _≈_

data _≈_  : {α : Ty} (x y : Tm α) → Set where
  ≈refl  : ∀ {α} {x : Tm α} →
             x ≈ x
  ≈sym   : ∀ {α} {x y : Tm α} →
             x ≈ y → y ≈ x
  ≈trans : ∀ {α} {x y z : Tm α} →
             x ≈ y → y ≈ z → x ≈ z
  ≈K     : ∀ {α β} {x : Tm α} {y : Tm β} →
             K ∙ x ∙ y ≈ x
  ≈S     : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
             S ∙ x ∙ y ∙ z ≈ (x ∙ z) ∙ (y ∙ z)
  ≈cong∙ : ∀ {α β} {x₁ x₂ : Tm (α ⇒ β)} {y₁ y₂ : Tm α} →
             x₁ ≈ x₂ → y₁ ≈ y₂ → x₁ ∙ y₁ ≈ x₂ ∙ y₂

≈setoid : {α : Ty} → Setoid _ _

≈setoid {α} = record
  { Carrier = Tm α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {α : Ty} = EqReasoning (≈setoid {α})

--
-- Normal forms.
-- 

data Nf : Ty → Set where
  K0 : ∀ {α β} →
         Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} (u : Nf α) →
         Nf (β ⇒ α)
  S0 : ∀ {α β γ} →
         Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) →
         Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β))→
         Nf (α ⇒ γ)

--
-- Reification.
--

⌜_⌝ : ∀ {α} (n : Nf α) → Tm α
⌜ K0 ⌝ = K
⌜ K1 u ⌝ = K ∙ ⌜ u ⌝
⌜ S0 ⌝ = S
⌜ S1 u ⌝ = S ∙ ⌜ u ⌝
⌜ S2 u v ⌝ = S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  infixl 5 _⟨∙⟩_

  {-# TERMINATING #-}

  _⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (w : Nf α) → Nf β
  K0 ⟨∙⟩ w = K1 w
  K1 u ⟨∙⟩ w = u
  S0 ⟨∙⟩ w = S1 w
  S1 u ⟨∙⟩ w = S2 u w
  S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧

  ⟦III⟧ : ⟦ III ⟧ ≡ S2 K0 K0
  ⟦III⟧ = refl

  norm : ∀ {α} → Tm α → Tm α
  norm = ⌜_⌝ ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- Normalization by evaluation with the delay monad.
--

infixl 5 _⟨∙⟩_

mutual

  _⟨∙⟩_ : ∀ {α β i} (u : Nf (α ⇒ β)) (v : Nf α) → Delay i (Nf β)

  K0 ⟨∙⟩ u = now (K1 u)
  K1 u ⟨∙⟩ v = now u
  S0 ⟨∙⟩ u = now (S1 u)
  S1 u ⟨∙⟩ v = now (S2 u v)
  S2 u v ⟨∙⟩ w = later (∞S u v w)

  ∞S : ∀ {α β γ i}
    (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β)) (w : Nf α) → ∞Delay i (Nf γ)
  force (∞S u v w) {j} =
    u ⟨∙⟩ w >>= λ uw → v ⟨∙⟩ w >>= λ vw → uw ⟨∙⟩ vw

  ⟦_⟧ : ∀ {α i} (x : Tm α) → Delay i (Nf α)

  ⟦ K ⟧ = now K0
  ⟦ S ⟧ = now S0
  ⟦ x ∙ y ⟧ =
    ⟦ x ⟧ >>= λ u → ⟦ y ⟧ >>= λ v → u ⟨∙⟩ v

dnorm : ∀ {α} (x : Tm α) → ∀ {i} → Delay i (Tm α)
dnorm x = ⌜_⌝ <$> ⟦ x ⟧

dnorm-III⇓ : dnorm III ⇓ (S ∙ K ∙ K)
dnorm-III⇓ = later⇓ (later⇓ now⇓)

--
-- "Strong computability" of normal forms.
--

SC : ∀ {α} (u : Nf α) → Set
SC {⋆} u = ⊤
SC {α ⇒ β} u = ∀ (v : Nf α) (q : SC v) →
    ∃ λ w → u ⟨∙⟩ v ⇓ w × ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝ × SC w

mutual

  all-sc : ∀ {α} (x : Tm α) → ∃ λ u → ⟦ x ⟧ ⇓ u × SC u
  all-sc K =
    K0 , now⇓ , λ u p →
      K1 u , now⇓ , ≈refl , λ v q →
        u , now⇓ , ≈K , p
  all-sc S =
    S0 , now⇓ , λ u p →
      S1 u , now⇓ , ≈refl , λ v q →
        S2 u v , now⇓ , ≈refl ,
          all-sc-S3 u p v q
  all-sc (x ∙ y)
    with all-sc x | all-sc y
  ... | u , ⇓u , p | v , ⇓v , q
    with p v q
  ... | uv , ⇓uv , ≈uv , pq
    = uv , bind⇓₂ _⟨∙⟩_ ⇓u ⇓v ⇓uv , pq

  all-sc-S3 : ∀ {α} {β} {γ}
    (u : Nf (α ⇒ β ⇒ γ)) (p : SC u) (v : Nf (α ⇒ β)) (q : SC v) →
    SC (S2 u v)
  all-sc-S3 u p v q w r
    with p w r | q w r
  ... | uw , ⇓uw , ≈uw , pr | vw , ⇓vw , ≈vw , qr
    with pr vw qr
  ... | uwvw , ⇓uwvw , ≈uwvw , prqr
    = uwvw , later⇓ (bind⇓₂ _⟨∙⟩_ ⇓uw ⇓vw ⇓uwvw) , suvw≈uwvw , prqr
    where
    open ≈-Reasoning
    suvw≈uwvw : S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝ ≈ ⌜ uwvw ⌝
    suvw≈uwvw = begin
      S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝
        ≈⟨ ≈S ⟩
      (⌜ u ⌝ ∙ ⌜ w ⌝) ∙ (⌜ v ⌝ ∙ ⌜ w ⌝)
        ≈⟨ ≈cong∙ ≈uw ≈vw ⟩
      ⌜ uw ⌝ ∙ ⌜ vw ⌝
        ≈⟨ ≈uwvw ⟩
      ⌜ uwvw ⌝
      ∎

--
-- Normalizer.
--

nf : ∀ {α} (x : Tm α) → Nf α
nf x = proj₁ (all-sc x)

nf-III : nf III ≡ S2 K0 K0
nf-III = refl

norm : ∀ {α} (x : Tm α) → Tm α
norm = ⌜_⌝ ∘ nf

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl

--
-- Stability: nf ⌜ n ⌝ ≡ n .
--

stable : ∀ {α} (u : Nf α) → nf ⌜ u ⌝ ≡ u

stable K0 = refl
stable (K1 u)
  rewrite stable u
  = refl
stable S0 = refl
stable (S1 u)
  rewrite stable u
  = refl
stable (S2 u v) = begin
  nf (S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝)
    ≡⟨⟩
  S2 (nf ⌜ u ⌝) (nf ⌜ v ⌝)
    ≡⟨ cong₂ S2 (stable u) (stable v) ⟩
  S2 u v
  ∎
  where open ≡-Reasoning

--
-- Completeness: x ≈ norm x
-- (Terms are convertible to their normal forms.)
--

norm-complete : ∀ {α} (x : Tm α) → x ≈ norm x

norm-complete K = ≈refl
norm-complete S = ≈refl
norm-complete (x ∙ y)
  with all-sc x | inspect all-sc x | all-sc y | inspect all-sc y
... | u , ⇓u , p | ≡[ all-sc-x≡ ] | v , ⇓v , q | ≡[ all-sc-y≡ ]
  with all-sc (x ∙ y) | p v q
... | w , ⇓w , pq | w′ , ⇓w′ , ≈w′ , pq′
  rewrite ⇓-det ⇓w′ (⇓bind₂ _⟨∙⟩_ ⇓u ⇓v ⇓w)
  = begin
  x ∙ y
    ≈⟨ ≈cong∙ (norm-complete x) (norm-complete y) ⟩
  norm x ∙ norm y
    ≡⟨ cong₂ _∙_ (cong (⌜_⌝ ∘ proj₁) all-sc-x≡)
                 (cong (⌜_⌝ ∘ proj₁) all-sc-y≡) ⟩
  ⌜ u ⌝ ∙ ⌜ v ⌝
    ≈⟨ ≈w′ ⟩
  ⌜ w ⌝
  ∎
  where open ≈-Reasoning


--
-- Soundness: the normal forms of two convertible terms are equal
--     x₁ ≈ x₂ → norm x₁ ≡ norm x₂
--

nf-sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

nf-sound ≈refl = refl
nf-sound (≈sym y≈x) =
  sym $ nf-sound y≈x
nf-sound (≈trans x≈y y≈z) =
  trans (nf-sound x≈y) (nf-sound y≈z)
nf-sound ≈K = refl
nf-sound ≈S = refl
nf-sound (≈cong∙ {α} {β} {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂)
  with nf-sound x₁≈x₂ | nf-sound y₁≈y₂
... | u₁≡u₂ | v₁≡v₂
  with all-sc x₁ | all-sc x₂ | all-sc y₁ | all-sc y₂
... | u₁ , ⇓u₁ , p₁ | u₂ , ⇓u₂ , p₂ | v₁ , ⇓v₁ , q₁ | v₂ , ⇓v₂ , q₂
  with p₁ v₁ q₁ | p₂ v₂ q₂
... | w₁ , ⇓w₁ , r₁ | w₂ , ⇓w₂ , r₂
  rewrite u₁≡u₂ | v₁≡v₂
  = ⇓-det ⇓w₁ ⇓w₂

norm-sound : ∀ {α} {x₁ x₂ : Tm α} →
  x₁ ≈ x₂ → norm x₁ ≡ norm x₂

norm-sound x₁≈x₂ =
  cong ⌜_⌝ (nf-sound x₁≈x₂)
