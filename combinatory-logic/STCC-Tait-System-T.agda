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


module STCC-Tait-System-T where

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
  N   :  Ty
  _⇒_ : (α β : Ty) → Ty

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
  ∙-cong : ∀ {α β} {x y : Tm (α ⇒ β)} {x′ y′ : Tm α} →
             x ≈ y → x′ ≈ y′ → x ∙ x′ ≈ y ∙ y′
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

reify : ∀ {α} (n : Nf α) → Tm α

reify K0 = K
reify (K1 u) = K ∙ reify u
reify S0 = S
reify (S1 u) = S ∙ reify u
reify (S2 u v) = S ∙ reify u ∙ reify v
reify ZERO0 = ZERO
reify SUC0 = SUC
reify (SUC1 u) = SUC ∙ reify u
reify REC0 = REC
reify (REC1 u) = REC ∙ reify u
reify (REC2 u v) = REC ∙ reify u ∙ reify v

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
  norm = reify ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

  norm-1+1 : norm (add (SUC ∙ ZERO) (SUC ∙ ZERO)) ≡ SUC ∙ (SUC ∙ ZERO)
  norm-1+1 = refl

--
-- Big-step reduction.
--

-- Since Agda's termination checker is unable to prove that
-- the "naive" normalazation function is total, let's rewrite
-- this function in form of a relation.

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
  ∙⇓ : ∀ {α β : Ty} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  ZERO⇓ :
    ZERO ⇓ ZERO0
  SUC⇓ :
    SUC ⇓ SUC0
  REC⇓ : ∀ {α} →
    REC {α} ⇓ REC0

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
⇓-det (∙⇓ p q r) (∙⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⇓-det ZERO⇓ ZERO⇓ = refl
⇓-det SUC⇓ SUC⇓ = refl
⇓-det REC⇓ REC⇓ = refl

--
-- Soundness: terms are convertible to their normal forms
--     x ⇓ u → x ≈ reify u
-- 

⟨∙⟩⇓-sound : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w : Nf β} →
  u ⟨∙⟩ v ⇓ w → reify u ∙ reify v ≈ reify w
⟨∙⟩⇓-sound K0⇓ = ≈refl
⟨∙⟩⇓-sound K1⇓ = ≈K
⟨∙⟩⇓-sound S0⇓ = ≈refl
⟨∙⟩⇓-sound S1⇓ = ≈refl
⟨∙⟩⇓-sound (S2⇓ {u = u} {v} {w} {w′} {w′′} {w′′′} p q r) = begin
  S ∙ reify u ∙ reify v ∙ reify w
    ≈⟨ ≈S ⟩
  (reify u ∙ reify w) ∙ (reify v ∙ reify w)
    ≈⟨ ∙-cong (⟨∙⟩⇓-sound p) (⟨∙⟩⇓-sound q) ⟩
  reify w′ ∙ reify w′′
    ≈⟨ ⟨∙⟩⇓-sound r ⟩
  reify w′′′
  ∎
  where open ≈-Reasoning
⟨∙⟩⇓-sound SUC0⇓ = ≈refl
⟨∙⟩⇓-sound REC0⇓ = ≈refl
⟨∙⟩⇓-sound REC1⇓ = ≈refl
⟨∙⟩⇓-sound REC2Z⇓ = ≈RZ
⟨∙⟩⇓-sound (REC2S⇓ {α} {u} {v} {w} {w′} {w′′} {w′′′} p q r) = begin
  REC ∙ reify u ∙ reify v ∙ (SUC ∙ reify w)
    ≈⟨ ≈RS ⟩
  (reify v ∙ reify w) ∙ (REC ∙ reify u ∙ reify v ∙ reify w)
    ≡⟨ refl ⟩
  (reify v ∙ reify w) ∙ (reify (REC2 u v) ∙ reify w)
    ≈⟨ ∙-cong (⟨∙⟩⇓-sound p) (⟨∙⟩⇓-sound q) ⟩
  reify w′ ∙ reify w′′
    ≈⟨ ⟨∙⟩⇓-sound r ⟩
  reify w′′′
  ∎
  where open ≈-Reasoning


⇓-sound : ∀ {α} {x : Tm α} {u : Nf α} →
  x ⇓ u → x ≈ reify u
⇓-sound K⇓ = ≈refl
⇓-sound S⇓ = ≈refl
⇓-sound (∙⇓ {x = x} {y} {u} {v} {uv} x⇓u y⇓v ⇓uv) = begin
  x ∙ y
    ≈⟨ ∙-cong (⇓-sound x⇓u) (⇓-sound y⇓v) ⟩
  reify u ∙ reify v
    ≈⟨ ⟨∙⟩⇓-sound ⇓uv ⟩
  reify uv
  ∎
  where open ≈-Reasoning
⇓-sound ZERO⇓ = ≈refl
⇓-sound SUC⇓ = ≈refl
⇓-sound REC⇓ = ≈refl

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
SCN {N} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v → ∃ λ w → u ⟨∙⟩ v ⇓ w × SCN w

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K2 : ∀ {α β} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → K1 {α} {β} u ⟨∙⟩ v ⇓ w × SCN w
all-scn-K2 u p v q =
  u , K1⇓ , p

all-scn-K1 : ∀ {α β} u (p : SCN u) →
  ∃ λ w → K0 {α} {β} ⟨∙⟩ u ⇓ w × SCN w
all-scn-K1 u p =
  K1 u , K0⇓ , all-scn-K2 u p

all-scn-S3 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) w (r : SCN w) →
  ∃ λ w′ → S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′ × SCN w′
all-scn-S3 u p v q w r =
  let w₁ , ⇓w₁ , r₁ = p w r
      w₂ , ⇓w₂ , r₂ = q w r
      w₃ , ⇓w₃ , r₃ = r₁ w₂ r₂
  in w₃ , S2⇓ ⇓w₁ ⇓w₂ ⇓w₃ , r₃

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → S1 {α} {β} {γ} u ⟨∙⟩ v ⇓ w × SCN w
all-scn-S2 u p v q =
  S2 u v , S1⇓ , all-scn-S3 u p v q

all-scn-S1 : ∀ {α β γ} u (p : SCN u) →
  ∃ λ w → S0 {α} {β} {γ} ⟨∙⟩ u ⇓ w × SCN w
all-scn-S1 u p =
  S1 u , S0⇓ , all-scn-S2 u p

all-scn-SUC1 : ∀ u (p : SCN u) →
  ∃ (λ w → SUC0 ⟨∙⟩ u ⇓ w × SCN w)
all-scn-SUC1 u tt =
  SUC1 u , SUC0⇓ , tt

all-scn-REC3 : ∀ {α} u (p : SCN u) v (q : SCN v) w (r : SCN w) →
  ∃ λ w′ → REC2 {α} u v ⟨∙⟩ w ⇓ w′ × SCN w′
all-scn-REC3 u p v q ZERO0 tt =
  u , REC2Z⇓ , p
all-scn-REC3 u p v q (SUC1 w) tt =
  let w₁ , ⇓w₁ , r₁ = q w tt
      w₂ , ⇓w₂ , r₂ = all-scn-REC3 u p v q w tt
      w₃ , ⇓w₃ , r₃ = r₁ w₂ r₂
  in w₃ , REC2S⇓ ⇓w₁ ⇓w₂ ⇓w₃ , r₃

all-scn-REC2 : ∀ {α} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → REC1 {α} u ⟨∙⟩ v ⇓ w × SCN w
all-scn-REC2 u p v q =
  REC2 u v , REC1⇓ , all-scn-REC3 u p v q

all-scn-REC1 : ∀ {α} u (p : SCN u) →
  ∃ λ w → REC0 {α} ⟨∙⟩ u ⇓ w × SCN w
all-scn-REC1 u p =
  REC1 u , REC0⇓ , all-scn-REC2 u p

-- ∀ {α} (u : Nf α) → SCN u

all-scn : ∀ {α} (u : Nf α) → SCN u

all-scn K0 =
  all-scn-K1
all-scn (K1 u) =
  all-scn-K2 u (all-scn u)
all-scn S0 =
  all-scn-S1
all-scn (S1 u) =
  all-scn-S2 u (all-scn u)
all-scn (S2 u v) =
  all-scn-S3 u (all-scn u) v (all-scn v)
all-scn ZERO0 =
  tt
all-scn SUC0 =
  all-scn-SUC1
all-scn (SUC1 u) =
  tt
all-scn REC0 =
  all-scn-REC1
all-scn (REC1 u) =
  all-scn-REC2 u (all-scn u)
all-scn (REC2 u v) =
  all-scn-REC3 u (all-scn u) v (all-scn v)

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (t : Tm α) → Set
SC t = ∃ λ u → t ⇓ u × SCN u

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , K⇓ , all-scn-K1
all-sc S =
  S0 , S⇓ , all-scn-S1
all-sc (x ∙ y) =
  let u , ⇓u , p = all-sc x
      v , ⇓v , q = all-sc y
      w , ⇓w , r = p v q
  in w , ∙⇓ ⇓u ⇓v ⇓w , r
all-sc ZERO =
  ZERO0 , ZERO⇓ , tt
all-sc SUC =
  SUC0 , SUC⇓ , all-scn-SUC1
all-sc REC =
  REC0 , REC⇓ , all-scn-REC1

--
-- Completeness: the normal forms of two convertible terms are equal
--     x ≈ y → x ⇓ u → y ⇓ v → u ≡ v
--

⇓-complete : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-complete ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-complete (≈sym x≈y) x⇓u x⇓v =
  sym $ ⇓-complete x≈y x⇓v x⇓u
⇓-complete (≈trans {α} {x} {z} {y} x≈z z≈y) x⇓u y⇓v =
  let w , z⇓w , r = all-sc z
  in trans (⇓-complete x≈z x⇓u z⇓w) (⇓-complete z≈y z⇓w y⇓v)
⇓-complete ≈K (∙⇓ (∙⇓ K⇓ x⇓′ K0⇓) y⇓ K1⇓) x⇓′′ =
  ⇓-det x⇓′ x⇓′′
⇓-complete ≈S
  (∙⇓ (∙⇓ (∙⇓ S⇓ x⇓ S0⇓) y⇓ S1⇓) z⇓ (S2⇓ ⇓uw ⇓vw ⇓uwvw))
  xzyz⇓ =
  ⇓-det (∙⇓ (∙⇓ x⇓ z⇓ ⇓uw) (∙⇓ y⇓ z⇓ ⇓vw) ⇓uwvw) xzyz⇓
⇓-complete (∙-cong x≈y x′≈y′) (∙⇓ x⇓u x′⇓u′ ⇓uv) (∙⇓ y⇓v y′⇓v′ ⇓u′v′)
  rewrite ⇓-complete x≈y x⇓u y⇓v | ⇓-complete x′≈y′ x′⇓u′ y′⇓v′
  = ⟨∙⟩⇓-det ⇓uv ⇓u′v′
⇓-complete ≈RZ
  (∙⇓ (∙⇓ (∙⇓ REC⇓ x⇓u REC0⇓) x⇓v REC1⇓) ZERO⇓ REC2Z⇓) x⇓u′ =
  ⇓-det x⇓u x⇓u′
⇓-complete ≈RS
  (∙⇓ (∙⇓ (∙⇓ REC⇓ p1 REC0⇓) p2 REC1⇓) (∙⇓ SUC⇓ p3 SUC0⇓)
    (REC2S⇓ p5 p4 p6))
  (∙⇓ (∙⇓ q7 q8 q5) (∙⇓ (∙⇓ (∙⇓ REC⇓ q1 REC0⇓) q2 REC1⇓) q3 q4) q6)
  rewrite ⇓-det p1 q1 | ⇓-det p2 q2 | ⇓-det p3 q3 | ⟨∙⟩⇓-det p4 q4
        | ⇓-det q2 q7 | ⇓-det q3 q8 | ⟨∙⟩⇓-det p5 q5 | ⟨∙⟩⇓-det p6 q6
  = refl

--
-- All terms are normalizable.
--    ∀ x → ∃ λ u → x ⇓ u
--

all-⇓ : ∀ {α} (x : Tm α) → ∃ λ u → x ⇓ u
all-⇓ x =
  let u , ⇓u , p = all-sc x
  in u , ⇓u

module TerminatingNorm where

  norm : ∀ {α} → Tm α → Tm α
  norm x = reify (proj₁ (all-⇓ x))

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

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
-- the original function `⟦_⟧` (and `⟦_⟧` is total).
--

-- apply

mutual

  apply : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
    {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w
  apply K0 u K0⇓ = K1 u , refl
  apply (K1 u) v K1⇓ = u , refl
  apply S0 u S0⇓ = S1 u , refl
  apply (S1 u) v S1⇓ = S2 u v , refl
  apply (S2 u v) w (S2⇓ uw⇓ vw⇓ uwvw⇓) =
    apply≡ (apply u w uw⇓) (apply v w vw⇓) uwvw⇓
  apply SUC0 u SUC0⇓ = SUC1 u , refl
  apply REC0 u REC0⇓ = REC1 u , refl
  apply (REC1 u) v REC1⇓ = REC2 u v , refl
  apply (REC2 u v) .ZERO0 REC2Z⇓ = u , refl
  apply (REC2 u v) ._ (REC2S⇓ {w = w} ⇓w′ ⇓w′′ ⇓w′′′) =
    apply≡ (apply v w ⇓w′) (apply (REC2 u v) w ⇓w′′) ⇓w′′′

  apply≡ : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α}
    (p : ∃ λ u′ → u′ ≡ u) (q : ∃ λ v′ → v′ ≡ v) {w} →
    u ⟨∙⟩ v ⇓ w → ∃ (λ w′ → w′ ≡ w)
  apply≡ (u′ , u′≡u) (v′ , v′≡v) ⇓w
    rewrite sym $ u′≡u | sym $ v′≡v
    = apply u′ v′ ⇓w

-- eval

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (∙⇓ x⇓ y⇓ ⇓w) =
  apply≡ (eval x x⇓) (eval y y⇓) ⇓w
eval ZERO ZERO⇓ = ZERO0 , refl
eval SUC SUC⇓ = SUC0 , refl
eval REC REC⇓ = REC0 , refl


module BoveCaprettaNorm where

  norm : ∀ {α} → Tm α → Tm α
  norm x =
    let u , x⇓u = all-⇓ x
    in reify (proj₁ (eval x x⇓u))

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl
