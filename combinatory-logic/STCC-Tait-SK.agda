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
open import Data.Unit using (⊤; tt) public
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
  ≈cong∙ : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y y′ : Tm α} →
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
--
-- _⇓_ will be shown to satisfy two requirements:
--
-- Determinism: x ⇓ u → x ⇓ v → u ≡ v
-- Totality:    ∀ x → ∃ λ u → x ⇓ u


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
  A⇓ : ∀ {α β : Ty} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w


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

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w) with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w

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

⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′
⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (A⇓ p q r) (A⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl


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

-- x ≈ y → nf x ≡ nf y

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , p , ⇓u | v , q , ⇓v
  with eval x ⇓u | eval y ⇓v
... | ._ , refl | ._ , refl
  = ⇓-sound x≈y ⇓u ⇓v
