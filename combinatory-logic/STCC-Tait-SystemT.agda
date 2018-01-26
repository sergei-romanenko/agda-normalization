{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  Based on

    Ana Bove and Venanzio Capretta. 2001.
    Nested General Recursion and Partiality in Type Theory.
    In Proceedings of the 14th International Conference on Theorem Proving
    in Higher Order Logics (TPHOLs '01),
    Richard J. Boulton and Paul B. Jackson (Eds.).
    Springer-Verlag, London, UK, UK, 121-135. 

  and

    Thorsten Altenkirch and James Chapman. 2006.
    Tait in one big step.
    In Proceedings of the 2006 international conference on Mathematically
    Structured Functional Programming (MSFP'06),
    Conor McBride and Tarmo Uustalu (Eds.).
    British Computer Society, Swinton, UK, UK, 4-4. 

-}


module STCC-Tait-SystemT where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Function
import Function.Related as Related

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   : Ty
  _⇒_ : (α β : Ty) → Ty
  N   :  Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  ZERO : Tm N
  SUC  : Tm (N ⇒ N)
  REC  : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (N ⇒ N)
III = I {N ⇒ N} ∙ (I {N ⇒ N} ∙ I {N})

#2 : Tm N
#2 = SUC ∙ (SUC ∙ ZERO)

-- suc1 x y = suc x

suc1 : Tm (N ⇒ N ⇒ N)
suc1 = S ∙ (K ∙ K) ∙ SUC

-- suc2 x y = suc y

suc2 : Tm (N ⇒ N ⇒ N)
suc2 = K ∙ SUC

-- add x y = x + y

add : Tm N → Tm N → Tm N
add m n = REC ∙ n ∙ (K ∙ SUC) ∙ m

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
  ≈cong∙ : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y y′ : Tm α} →
    x ≈ x′ → y ≈ y′ → x ∙ y ≈ x′ ∙ y′
  ≈RZ    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
    REC ∙ x ∙ y ∙ ZERO ≈ x 
  ≈RS    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
    REC ∙ x ∙ y ∙ (SUC ∙ z) ≈ y ∙ z ∙ (REC ∙ x ∙ y ∙ z)

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
  ZERO0 : Nf N
  SUC0  : Nf (N ⇒ N)
  SUC1  : ∀ (u : Nf N) →
            Nf N
  REC0  : ∀ {α} →
            Nf (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
  REC1  : ∀ {α} (u : Nf α) →
            Nf ((N ⇒ α ⇒ α) ⇒ N ⇒ α)
  REC2  : ∀ {α} (u : Nf α) (v : Nf (N ⇒ α ⇒ α)) →
            Nf (N ⇒ α)

⌜_⌝ : ∀ {α} (n : Nf α) → Tm α

⌜ K0 ⌝ = K
⌜ K1 u ⌝ = K ∙ ⌜ u ⌝
⌜ S0 ⌝ = S
⌜ S1 u ⌝ = S ∙ ⌜ u ⌝
⌜ S2 u v ⌝ = S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝
⌜ ZERO0 ⌝ = ZERO
⌜ SUC0 ⌝ = SUC
⌜ SUC1 u ⌝ = SUC ∙ ⌜ u ⌝
⌜ REC0 ⌝ = REC
⌜ REC1 u ⌝ = REC ∙ ⌜ u ⌝
⌜ REC2 u v ⌝ = REC ∙ ⌜ u ⌝ ∙ ⌜ v ⌝

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
  SUC0 ⟨∙⟩ w = SUC1 w
  REC0 ⟨∙⟩ w = REC1 w
  REC1 u ⟨∙⟩ w = REC2 u w
  REC2 u v ⟨∙⟩ ZERO0 = u
  REC2 u v ⟨∙⟩ SUC1 w = v ⟨∙⟩ w ⟨∙⟩ (REC2 u v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
  ⟦ ZERO ⟧ = ZERO0
  ⟦ SUC ⟧ = SUC0
  ⟦ REC ⟧ = REC0

  norm : ∀ {α} → Tm α → Tm α
  norm = ⌜_⌝ ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

  norm-1+1 : norm (add (SUC ∙ ZERO) (SUC ∙ ZERO)) ≡ SUC ∙ (SUC ∙ ZERO)
  norm-1+1 = refl

--
-- Big-step reduction.
--

-- Since Agda's termination checker is unable to prove that
-- the "naive" normalazation function is total, let's rewrite
-- this function in form of a relation x ⇓ u, where
-- the intended meaning of x ⇓ u is ⟦ x ⟧ ≡ u .
--
-- _⇓_ will be shown to satisfy two requirements:
--
-- Determinism: x ⇓ u → x ⇓ v → u ≡ v
-- Totality:    ∀ x → ∃ λ u → x ⇓ u


infix 4 _⇓_ _⟨∙⟩_⇓_

data _⟨∙⟩_⇓_ : ∀ {α β} (x : Nf (α ⇒ β)) (y : Nf α) (u : Nf β) → Set where
  K0⇓ : ∀ {α β w} →
    K0 {α} {β} ⟨∙⟩ w ⇓ K1 w
  K1⇓ : ∀ {α β u w} →
    K1 {α} {β} u ⟨∙⟩ w ⇓ u
  S0⇓ : ∀ {α β γ w} →
    S0 {α} {β} {γ} ⟨∙⟩ w ⇓ S1 w
  S1⇓ : ∀ {α β γ u w} →
    S1 {α} {β} {γ} u ⟨∙⟩ w ⇓ S2 u w
  S2⇓ : ∀ {α β γ u v w w′ w′′ w′′′}
    (p : u ⟨∙⟩ w ⇓ w′) (q : v ⟨∙⟩ w ⇓ w′′) (r : w′ ⟨∙⟩ w′′ ⇓ w′′′) →
    S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′′′
  SUC0⇓ : ∀ {w} →
    SUC0 ⟨∙⟩ w ⇓ SUC1 w
  REC0⇓ : ∀ {α w} →
    REC0 {α} ⟨∙⟩ w ⇓ REC1 w
  REC1⇓  : ∀ {α u w} →
    REC1 {α} u ⟨∙⟩ w ⇓ REC2 u w
  REC2Z⇓ : ∀ {α u v} →
    REC2 {α} u v ⟨∙⟩ ZERO0 ⇓ u
  REC2S⇓ : ∀ {α u v w w′ w′′ w′′′}
    (⇓w′ : v ⟨∙⟩ w ⇓ w′) (⇓w′′ : REC2 u v ⟨∙⟩ w ⇓ w′′) (⇓w′′′ : w′ ⟨∙⟩ w′′ ⇓ w′′′) →
    REC2 {α} u v ⟨∙⟩ SUC1 w ⇓ w′′′

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β : Ty} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ : Ty} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β : Ty} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  ZERO⇓ :
    ZERO ⇓ ZERO0
  SUC⇓ :
    SUC ⇓ SUC0
  REC⇓ : ∀ {α} →
    REC {α} ⇓ REC0


--
-- Now, as suggested by Bove and Capretta, we add to the normalization function
-- an additional argument: a proof of the existence of the normal form.
--
-- Since, unlike Coq, Agda doesn't make a distinction
-- between `Set` and `Prop`, it's not clear if the trick
-- by Bove and Capretta makes sense (for Agda)?
--
-- Probably, the answer is that, informally, it is easy to see that
-- the (following) function `eval` is an "instrumented" version of
-- the "naive" function `⟦_⟧`. And `eval` uses the propositional argument
-- neither for making decisions nor for producing the normal form.
-- Hence, the propositional argument can be removed to produce
-- the original function `⟦_⟧`.
--

--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
  {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w

K0 ⟨∙⟩ v & K0⇓ = K1 v , refl
K1 u ⟨∙⟩ v & K1⇓ = u , refl
S0 ⟨∙⟩ v & S0⇓ = S1 v , refl
S1 u ⟨∙⟩ v & S1⇓ = S2 u v , refl
S2 u v ⟨∙⟩ w & S2⇓ uw⇓ vw⇓ uwvw⇓ with u ⟨∙⟩ w & uw⇓ | v ⟨∙⟩ w & vw⇓
... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & uwvw⇓
SUC0 ⟨∙⟩ u & SUC0⇓ = SUC1 u , refl
REC0 ⟨∙⟩ u & REC0⇓ = REC1 u , refl
REC1 u ⟨∙⟩ v & REC1⇓ = REC2 u v , refl
REC2 u v ⟨∙⟩ ZERO0 & REC2Z⇓ = u , refl
REC2 u v ⟨∙⟩ SUC1 w & REC2S⇓ ⇓w′ ⇓w′′ ⇓w′′′
  with v ⟨∙⟩ w & ⇓w′ | REC2 u v  ⟨∙⟩ w & ⇓w′′
... | w′ , refl | w′′ , refl = w′ ⟨∙⟩ w′′ & ⇓w′′′

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w) with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
eval ZERO ZERO⇓ = ZERO0 , refl
eval SUC SUC⇓ = SUC0 , refl
eval REC REC⇓ = REC0 , refl

module BoveCaprettaNorm where

  postulate
    all-⇓ : ∀ {α} (x : Tm α) → ∃ λ u → x ⇓ u

  norm : ∀ {α} → Tm α → Tm α
  norm x with all-⇓ x
  ... | u , x⇓u =
    ⌜ proj₁ (eval x x⇓u) ⌝


--
-- Determinism: x ⇓ u → x ⇓ v → u ≡ v
--

⟨∙⟩⇓-det : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w w′ : Nf β} →
  u ⟨∙⟩ v ⇓ w → u ⟨∙⟩ v ⇓ w′ → w ≡ w′
⟨∙⟩⇓-det K0⇓ K0⇓ = refl
⟨∙⟩⇓-det K1⇓ K1⇓ = refl
⟨∙⟩⇓-det S0⇓ S0⇓ = refl
⟨∙⟩⇓-det S1⇓ S1⇓ = refl
⟨∙⟩⇓-det (S2⇓ p q r) (S2⇓ p′ q′ r′)
  rewrite ⟨∙⟩⇓-det p p′ | ⟨∙⟩⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⟨∙⟩⇓-det SUC0⇓ SUC0⇓ = refl
⟨∙⟩⇓-det REC0⇓ REC0⇓ = refl
⟨∙⟩⇓-det REC1⇓ REC1⇓ = refl
⟨∙⟩⇓-det REC2Z⇓ REC2Z⇓ = refl
⟨∙⟩⇓-det (REC2S⇓ p q r) (REC2S⇓ p′ q′ r′)
  rewrite ⟨∙⟩⇓-det p p′ | ⟨∙⟩⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl

⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′
⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (A⇓ p q r) (A⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⇓-det ZERO⇓ ZERO⇓ = refl
⇓-det SUC⇓ SUC⇓ = refl
⇓-det REC⇓ REC⇓ = refl


--
-- Now we are going to prove that
--     ∀ x → ∃ λ u → x ⇓ u
-- The main idea is to define a "Strong Computability" predicate
-- on normal forms by induction over types.
--

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set
SCN {⋆} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v →
  ∃ λ w → SCN w × (u ⟨∙⟩ v ⇓ w)
SCN {N} u = ⊤

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K1 : ∀ {α β} u (p : SCN u) → SCN (K1 {α} {β} u)
all-scn-K1 u p v q =
  u , p , K1⇓

all-scn-K0 : ∀ {α β} → SCN (K0 {α} {β})
all-scn-K0 u p =
  K1 u , all-scn-K1 u p , K0⇓

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (S2 {α} {β} {γ} u v)
all-scn-S2 u p v q w r with p w r | q w r
... | w₁ , r₁ , ⇓w₁ | w₂ , r₂ , ⇓w₂ with r₁ w₂ r₂
... | w₃ , r₃ , ⇓w₃ =
  w₃ , r₃ , S2⇓ ⇓w₁ ⇓w₂ ⇓w₃

all-scn-S1 : ∀ {α β γ} u (p : SCN u) → SCN (S1 {α} {β} {γ} u)
all-scn-S1 u p v q =
  S2 u v , all-scn-S2 u p v q , S1⇓

all-scn-S0 : ∀ {α β γ} → SCN (S0 {α} {β} {γ})
all-scn-S0 u p =
  S1 u , all-scn-S1 u p , S0⇓

all-scn-SUC0 : SCN (SUC0)
all-scn-SUC0 u tt =
  SUC1 u , tt , SUC0⇓

all-scn-REC2 : ∀ {α} u (p : SCN {α} u) v (q : SCN v) →
  SCN (REC2 u v)
all-scn-REC2 u p v q ZERO0 tt =
  u , p , REC2Z⇓
all-scn-REC2 u p v q (SUC1 w) tt
  with q w tt
... | w₁ , r₁ , ⇓w₁
  with all-scn-REC2 u p v q w tt
... | w₂ , r₂ , ⇓w₂
  with r₁ w₂ r₂
... | w₃ , r₃ , ⇓w₃ =
  w₃ , r₃ , REC2S⇓ ⇓w₁ ⇓w₂ ⇓w₃

all-scn-REC1 : ∀ {α} u (p : SCN {α} u) →
  SCN (REC1 u)
all-scn-REC1 u p v q =
  REC2 u v , all-scn-REC2 u p v q , REC1⇓

all-scn-REC0 : ∀ {α} →
  SCN (REC0 {α})
all-scn-REC0 u p =
  REC1 u , all-scn-REC1 u p , REC0⇓

-- ∀ {α} (u : Nf α) → SCN u

all-scn : ∀ {α} (u : Nf α) → SCN u

all-scn K0 =
  all-scn-K0
all-scn (K1 u) =
  all-scn-K1 u (all-scn u)
all-scn S0 =
  all-scn-S0
all-scn (S1 u) =
  all-scn-S1 u (all-scn u)
all-scn (S2 u v) =
  all-scn-S2 u (all-scn u) v (all-scn v)
all-scn ZERO0 =
  tt
all-scn SUC0 =
  all-scn-SUC0
all-scn (SUC1 u) =
  tt
all-scn REC0 =
  all-scn-REC0
all-scn (REC1 u) =
  all-scn-REC1 u (all-scn u)
all-scn (REC2 u v) =
  all-scn-REC2 u (all-scn u) v (all-scn v)

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (x : Tm α) → Set
SC x = ∃ λ u → SCN u × x ⇓ u

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , all-scn-K0 , K⇓
all-sc S =
  S0 , all-scn-S0 , S⇓
all-sc (x ∙ y) with all-sc x | all-sc y
... | u , p , ⇓u | v , q , ⇓v with p v q
... | w , r , ⇓w =
  w , r , A⇓ ⇓u ⇓v ⇓w
all-sc ZERO =
  ZERO0 , tt , ZERO⇓
all-sc SUC =
  SUC0 , all-scn-SUC0 , SUC⇓
all-sc REC =
  REC0 , all-scn-REC0 , REC⇓

--
-- All terms are normalizable.
--    ∀ x → ∃ λ u → x ⇓ u
--

all-⇓ : ∀ {α} (x : Tm α) → ∃ λ u → x ⇓ u
all-⇓ x with all-sc x
... | u , p , ⇓u =
  u , ⇓u

module ProofRelevantNormalizer where

  -- all-sc returns the result of normalization,
  -- thus we actually have a normilizer. Its drawback, however, is
  -- that computing the normal form is mixed with computing a proof.

  nf : ∀ {α} (x : Tm α) → Nf α

  nf x with all-sc x
  ... | u , p , x⇓u = u

--
-- Structurally recursive normalizer.
-- (The normal form is not produced from the proof.)
--

nf : ∀ {α} (x : Tm α) → Nf α

nf x with all-sc x
... | u , p , x⇓u with eval x x⇓u
... | u′ , u′≡u = u′

--
-- Completeness: terms are convertible to their normal forms.
-- 
-- u ⟨∙⟩ v ⇓ w → ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝

⟨∙⟩⇓-complete : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w : Nf β} →
  u ⟨∙⟩ v ⇓ w → ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝
⟨∙⟩⇓-complete K0⇓ = ≈refl
⟨∙⟩⇓-complete K1⇓ = ≈K
⟨∙⟩⇓-complete S0⇓ = ≈refl
⟨∙⟩⇓-complete S1⇓ = ≈refl
⟨∙⟩⇓-complete (S2⇓ {u = u} {v} {w} {w′} {w′′} {w′′′} p q r) = begin
  S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝
    ≈⟨ ≈S ⟩
  (⌜ u ⌝ ∙ ⌜ w ⌝) ∙ (⌜ v ⌝ ∙ ⌜ w ⌝)
    ≈⟨ ≈cong∙ (⟨∙⟩⇓-complete p) (⟨∙⟩⇓-complete q) ⟩
  ⌜ w′ ⌝ ∙ ⌜ w′′ ⌝
    ≈⟨ ⟨∙⟩⇓-complete r ⟩
  ⌜ w′′′ ⌝
  ∎
  where open ≈-Reasoning
⟨∙⟩⇓-complete SUC0⇓ = ≈refl
⟨∙⟩⇓-complete REC0⇓ = ≈refl
⟨∙⟩⇓-complete REC1⇓ = ≈refl
⟨∙⟩⇓-complete REC2Z⇓ = ≈RZ
⟨∙⟩⇓-complete (REC2S⇓ {α} {u} {v} {w} {w′} {w′′} {w′′′} p q r) = begin
  REC ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (SUC ∙ ⌜ w ⌝)
    ≈⟨ ≈RS ⟩
  (⌜ v ⌝ ∙ ⌜ w ⌝) ∙ (REC ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝)
    ≡⟨ refl ⟩
  (⌜ v ⌝ ∙ ⌜ w ⌝) ∙ (⌜ REC2 u v ⌝ ∙ ⌜  w ⌝)
    ≈⟨ ≈cong∙ (⟨∙⟩⇓-complete p) (⟨∙⟩⇓-complete q) ⟩
  ⌜ w′ ⌝ ∙ ⌜ w′′ ⌝
    ≈⟨ ⟨∙⟩⇓-complete r ⟩
  ⌜ w′′′ ⌝
  ∎
  where open ≈-Reasoning

-- x ⇓ u → x ≈ ⌜ u ⌝

⇓-complete : ∀ {α} {x : Tm α} {u : Nf α} →
  x ⇓ u → x ≈ ⌜ u ⌝
⇓-complete K⇓ = ≈refl
⇓-complete S⇓ = ≈refl
⇓-complete (A⇓ {x = x} {y} {u} {v} {uv} x⇓u y⇓v ⇓uv) = begin
  x ∙ y
    ≈⟨ ≈cong∙ (⇓-complete x⇓u) (⇓-complete y⇓v) ⟩
  ⌜ u ⌝ ∙ ⌜ v ⌝
    ≈⟨ ⟨∙⟩⇓-complete ⇓uv ⟩
  ⌜ uv ⌝
  ∎
  where open ≈-Reasoning
⇓-complete ZERO⇓ = ≈refl
⇓-complete SUC⇓ = ≈refl
⇓-complete REC⇓ = ≈refl

-- x ≈ ⌜ nf x ⌝

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝

complete x with all-sc x
... | u , p , x⇓u with eval x x⇓u
... | ._ , refl =
  ⇓-complete x⇓u


--
-- Soundness: normalization takes convertible terms to identical normal forms.
--

--     x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-sound {u = u} {v} (≈sym y≈x) x⇓u x⇓v = begin
  u ≡⟨ sym $ ⇓-sound y≈x x⇓v x⇓u ⟩ v ∎
  where open ≡-Reasoning
⇓-sound {u = u} {v} (≈trans {y = z} x≈z z≈y) x⇓u y⇓v
  with all-sc z
... | w , r , z⇓w = begin
  u
    ≡⟨ ⇓-sound x≈z x⇓u z⇓w ⟩
  w
    ≡⟨ ⇓-sound z≈y z⇓w y⇓v ⟩
  v
  ∎
  where open ≡-Reasoning
⇓-sound ≈K (A⇓ (A⇓ K⇓ x⇓′ K0⇓) y⇓ K1⇓) x⇓′′ =
  ⇓-det x⇓′ x⇓′′
⇓-sound ≈S
  (A⇓ (A⇓ (A⇓ S⇓ x⇓ S0⇓) y⇓ S1⇓) z⇓ (S2⇓ ⇓uw ⇓vw ⇓uwvw))
  xzyz⇓ =
  ⇓-det (A⇓ (A⇓ x⇓ z⇓ ⇓uw) (A⇓ y⇓ z⇓ ⇓vw) ⇓uwvw) xzyz⇓
⇓-sound (≈cong∙ x≈x′ y≈y′) (A⇓ ⇓u ⇓v ⇓uv) (A⇓ ⇓u′ ⇓v′ ⇓u′v′)
  rewrite ⇓-sound x≈x′ ⇓u ⇓u′ | ⇓-sound y≈y′ ⇓v ⇓v′  =
  ⟨∙⟩⇓-det ⇓uv ⇓u′v′
⇓-sound ≈RZ
  (A⇓ (A⇓ (A⇓ REC⇓ x⇓u REC0⇓) x⇓v REC1⇓) ZERO⇓ REC2Z⇓) x⇓u′ =
  ⇓-det x⇓u x⇓u′
⇓-sound ≈RS
  (A⇓ (A⇓ (A⇓ REC⇓ p1 REC0⇓) p2 REC1⇓) (A⇓ SUC⇓ p3 SUC0⇓)
    (REC2S⇓ p5 p4 p6))
  (A⇓ (A⇓ q7 q8 q5) (A⇓ (A⇓ (A⇓ REC⇓ q1 REC0⇓) q2 REC1⇓) q3 q4) q6)
  rewrite ⇓-det p1 q1 | ⇓-det p2 q2 | ⇓-det p3 q3 | ⟨∙⟩⇓-det p4 q4
        | ⇓-det q2 q7 | ⇓-det q3 q8 | ⟨∙⟩⇓-det p5 q5 | ⟨∙⟩⇓-det p6 q6
  = refl

-- x ≈ y → nf x ≡ nf y

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , p , ⇓u | v , q , ⇓v
  with eval x ⇓u | eval y ⇓v
... | ._ , refl | ._ , refl
  = ⇓-sound x≈y ⇓u ⇓v
