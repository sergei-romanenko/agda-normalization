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


module STCC-Tait-SK where

open import Data.Empty
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
  ∙-cong : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y y′ : Tm α} →
             x ≈ x′ → y ≈ y′ → x ∙ y ≈ x′ ∙ y′

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

⌜_⌝ : ∀ {α} (n : Nf α) → Tm α

⌜ K0 ⌝ = K
⌜ K1 u ⌝ = K ∙ ⌜ u ⌝
⌜ S0 ⌝ = S
⌜ S1 u ⌝ = S ∙ ⌜ u ⌝
⌜ S2 u v ⌝ = S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝

--
-- There is no non-functional normal form!
--

∄-Nf-⋆ : (u : Nf ⋆) → ⊥
∄-Nf-⋆ ()

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  infixl 5 _⟨∙⟩_

  {-# TERMINATING #-}

  _⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α) → Nf β
  K0 ⟨∙⟩ u = K1 u
  K1 u ⟨∙⟩ v = u
  S0 ⟨∙⟩ u = S1 u
  S1 u ⟨∙⟩ v = S2 u v
  S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧


  ⟦III⟧ : ⟦ III ⟧ ≡ S2 K0 (K0 {⋆} {⋆})
  ⟦III⟧ = refl

  norm : ∀ {α} → Tm α → Tm α
  norm = ⌜_⌝ ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- Big-step reduction.
--

-- Since Agda's termination checker is unable to prove that
-- the "naive" normalazation function is total, let's rewrite
-- this function in form of a relation.

infix 4 _⇓_ _⟨∙⟩_⇓_

data _⟨∙⟩_⇓_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α) (w : Nf β) → Set where
  K0⇓ : ∀ {α β u} →
    K0 {α} {β} ⟨∙⟩ u ⇓ K1 u
  K1⇓ : ∀ {α β u v} →
    K1 {α} {β} u ⟨∙⟩ v ⇓ u
  S0⇓ : ∀ {α β γ u} →
    S0 {α} {β} {γ} ⟨∙⟩ u ⇓ S1 u
  S1⇓ : ∀ {α β γ u v} →
    S1 {α} {β} {γ} u ⟨∙⟩ v ⇓ S2 u v
  S2⇓ : ∀ {α β γ u v w w′ w′′ w′′′}
    (p : u ⟨∙⟩ w ⇓ w′) (q : v ⟨∙⟩ w ⇓ w′′) (r : w′ ⟨∙⟩ w′′ ⇓ w′′′) →
    S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′′′

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β : Ty} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ : Ty} →
    S {α} {β} {γ} ⇓ S0
  ∙⇓ : ∀ {α β : Ty} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w

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
SCN {⋆} ()
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

--
-- All terms are normalizable.
--    ∀ x → ∃ λ u → x ⇓ u
--

all-⇓ : ∀ {α} (x : Tm α) → ∃ λ u → x ⇓ u
all-⇓ x =
  let u , ⇓u , p = all-sc x
  in u , ⇓u


--
-- Normalizer!
--

nf : ∀ {α} (x : Tm α) → Nf α
nf x with all-sc x
... | u , ⇓u , p = u


module TerminatingNorm where

  -- The proof of (∃ λ u → x ⇓ u) contains the result of evaluating x.
  -- Hence, we can extract and use it.

  norm : ∀ {α} → Tm α → Tm α
  norm x = ⌜ proj₁ (all-⇓ x) ⌝

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

  -- The problem with the above `norm` is that it's difficult to extract
  -- the recursive normalizer by removing the proof-related stuff.


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

⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′
⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (∙⇓ p q r) (∙⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl

--
-- Soundness: the normal forms of two convertible terms are equal.
--

-- x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-sound (≈sym x≈y) x⇓u x⇓v =
  sym $ ⇓-sound x≈y x⇓v x⇓u
⇓-sound (≈trans {α} {x} {z} {y} x≈z z≈y) x⇓u y⇓v =
  let w , z⇓w , r = all-sc z
  in trans (⇓-sound x≈z x⇓u z⇓w) (⇓-sound z≈y z⇓w y⇓v)
⇓-sound ≈K (∙⇓ (∙⇓ K⇓ x⇓′ K0⇓) y⇓ K1⇓) x⇓′′ =
  ⇓-det x⇓′ x⇓′′
⇓-sound ≈S
  (∙⇓ (∙⇓ (∙⇓ S⇓ x⇓ S0⇓) y⇓ S1⇓) z⇓ (S2⇓ ⇓uw ⇓vw ⇓uwvw))
  xzyz⇓ =
  ⇓-det (∙⇓ (∙⇓ x⇓ z⇓ ⇓uw) (∙⇓ y⇓ z⇓ ⇓vw) ⇓uwvw) xzyz⇓
⇓-sound (∙-cong x≈x′ y≈y′) (∙⇓ ⇓u ⇓v ⇓uv) (∙⇓ ⇓u′ ⇓v′ ⇓u′v′)
  rewrite ⇓-sound x≈x′ ⇓u ⇓u′ | ⇓-sound y≈y′ ⇓v ⇓v′  =
  ⟨∙⟩⇓-det ⇓uv ⇓u′v′

-- x ≈ y → nf x ≡ nf y

nf-sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

nf-sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , ⇓u , p | v , ⇓v , q =
  ⇓-sound x≈y ⇓u ⇓v


--
-- Completeness: terms are convertible to their normal forms.
-- 

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
    ≈⟨ ∙-cong (⟨∙⟩⇓-complete p) (⟨∙⟩⇓-complete q) ⟩
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
⇓-complete (∙⇓ {x = x} {y} {u} {v} {uv} x⇓u y⇓v ⇓uv) = begin
  x ∙ y
    ≈⟨ ∙-cong (⇓-complete x⇓u) (⇓-complete y⇓v) ⟩
  ⌜ u ⌝ ∙ ⌜ v ⌝
    ≈⟨ ⟨∙⟩⇓-complete ⇓uv ⟩
  ⌜ uv ⌝
  ∎
  where open ≈-Reasoning

-- x ≈ ⌜ nf x ⌝

nf-complete : ∀ {α} (x : Tm α) →
  x ≈ ⌜ nf x ⌝
nf-complete x with all-sc x
... | u , ⇓u , p =
  ⇓-complete ⇓u


--
-- Now, as suggested by Bove and Capretta, we add to the normalization function
-- an additional argument: a proof of the existence of the normal form.
--
-- Since, unlike Coq, Agda doesn't make a distinction
-- between `Set` and `Prop`, it's not clear if the trick
-- by Bove and Capretta makes sense (for Agda)?
--
-- Probably, the answer is that, informally, it is easy to see that
-- the (following) function `⟦_⟧&_` is an "instrumented" version of
-- the "naive" function `⟦_⟧`. And `⟦_⟧&_` uses the propositional argument
-- neither for making decisions nor for producing the normal form.
-- Hence, the propositional argument can be removed to produce
-- the original function `⟦_⟧` (and, hence `⟦_⟧` is total).
--

-- Structurally recursive evaluator.

-- _⟨∙⟩_&_

mutual

  _⟨∙⟩_&_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
    {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w
  --K0 ⟨∙⟩ u & K0⇓ = K1 u , refl
  K0 ⟨∙⟩ u & r with r
  ... | K0⇓ = K1 u , refl
  K1 u ⟨∙⟩ v & K1⇓ = u , refl
  S0 ⟨∙⟩ u & S0⇓ = S1 u , refl
  S1 u ⟨∙⟩ v & S1⇓ = S2 u v , refl
  S2 u v ⟨∙⟩ w & S2⇓ uw⇓ vw⇓ uwvw⇓ =
    apply& (u ⟨∙⟩ w & uw⇓) (v ⟨∙⟩ w & vw⇓) uwvw⇓

  apply& : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α}
    (p : ∃ λ u′ → u′ ≡ u) (q : ∃ λ v′ → v′ ≡ v) {w} (⇓w : u ⟨∙⟩ v ⇓ w) →
      ∃ (λ w′ → w′ ≡ w)
  apply& (u′ , refl) (v′ , refl) ⇓w =
    u′ ⟨∙⟩ v′ & ⇓w

⟦_⟧&_ : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

⟦ K ⟧& K⇓ = K0 , refl
⟦ S ⟧& S⇓ = S0 , refl
⟦ x ∙ y ⟧& ∙⇓ x⇓ y⇓ ⇓w =
  apply& (⟦ x ⟧& x⇓) (⟦ y ⟧& y⇓) ⇓w


module BoveCaprettaNorm where

  norm : ∀ {α} (x : Tm α) → Tm α
  norm x =
    let u , x⇓u = all-⇓ x
    in ⌜ proj₁ (⟦ x ⟧& x⇓u) ⌝

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl


nf-bk : ∀ {α} (x : Tm α) → Nf α
nf-bk x with all-sc x
... | u , ⇓u , p with ⟦ x ⟧& ⇓u
... | u′ , u′≡u = u′

nf≡nf-bk : ∀ {α} (x : Tm α) → nf x ≡ nf-bk x
nf≡nf-bk x with all-sc x
... | u , ⇓u , p with ⟦ x ⟧& ⇓u
nf≡nf-bk K | u , ⇓u , p | u′ , u′≡u = sym u′≡u
nf≡nf-bk S | u , ⇓u , p | u′ , u′≡u = sym u′≡u
nf≡nf-bk (x ∙ y) | u , ⇓u , p | u′ , u′≡u = sym u′≡u
