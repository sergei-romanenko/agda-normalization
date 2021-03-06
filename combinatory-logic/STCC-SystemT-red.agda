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

-}

module STCC-SystemT-red where

open import Agda.Primitive

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Star as Star
open import Data.Star.Properties

open import Function
import Function.Related as Related

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Rel; Setoid)

import Relation.Binary.EqReasoning as EqReasoning

open import STCC-SystemT-norm

--
-- Reduction.
--

infix 4 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K : ∀ {α β} {x : Tm α} {y : Tm β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶AL : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y   : Tm α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y
  ⟶AR : ∀ {α β} {x : Tm (α ⇒ β)} {y y′ : Tm α} →
            y ⟶ y′  →  x ∙ y ⟶ x ∙ y′
  ⟶RZ : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
            REC ∙ x ∙ y ∙ ZERO ⟶ x 
  ⟶RS : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
            REC ∙ x ∙ y ∙ (SUC ∙ z) ⟶ y ∙ z ∙ (REC ∙ x ∙ y ∙ z)

--
-- `Irreducible x` means that no rule is applicable.
--

Irreducible : ∀ {α} (x : Tm α) → Set
Irreducible x = ∄ (λ y → x ⟶ y)

-- Irreducible (reify u)

reify→irr : ∀ {α} (u : Nf α) → Irreducible (reify u)

reify→irr K0 (y , ())

reify→irr (K1 u) (._ , ⟶AL ())
reify→irr (K1 u) (._ , ⟶AR ⟶y) =
  reify→irr u (, ⟶y)
reify→irr S0 (y , ())
reify→irr (S1 u) (._ , ⟶AL ())
reify→irr (S1 u) (._ , ⟶AR ⟶y) =
  reify→irr u (, ⟶y)
reify→irr (S2 u v) (._ , ⟶AL (⟶AL ()))
reify→irr (S2 u v) (._ , ⟶AL (⟶AR ⟶y)) =
  reify→irr u (, ⟶y)
reify→irr (S2 u v) (._ , ⟶AR ⟶y) =
  reify→irr v (, ⟶y)
reify→irr ZERO0 (y , ())
reify→irr SUC0 (y , ())
reify→irr (SUC1 u) (._ , ⟶AL ())
reify→irr (SUC1 u) (._ , ⟶AR ⟶y) =
 reify→irr u (, ⟶y)
reify→irr REC0 (y , ())
reify→irr (REC1 u) (._ , ⟶AL ())
reify→irr (REC1 u) (._ , ⟶AR ⟶y) =
  reify→irr u (, ⟶y)
reify→irr (REC2 u v) (._ , ⟶AL (⟶AL ()))
reify→irr (REC2 u v) (._ , ⟶AL (⟶AR ⟶y)) =
  reify→irr u (, ⟶y)
reify→irr (REC2 u v) (._ , ⟶AR ⟶y) =
  reify→irr v (, ⟶y)

-- Irreducible (norm x)

norm→irr : ∀ {α} (x : Tm α) → Irreducible (norm x)
norm→irr x = reify→irr ⌈ ⟦ x ⟧ ⌉

-- Reflexive and transitive closure of _⟶_ .

infix 4 _⟶⋆_

_⟶⋆_ : ∀ {α} → Rel (Tm α) lzero
_⟶⋆_ {α} = Star (_⟶_ {α})

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Tm α) → I {α} ∙ x ⟶⋆ x
reduction-example x = ⟶S ◅ ⟶K ◅ ε

-- Example: 1 + 1.

1+1 : add (SUC ∙ ZERO) (SUC ∙ ZERO) ⟶⋆ SUC ∙ (SUC ∙ ZERO)
1+1 = ⟶RS ◅ ⟶AL ⟶K ◅ ⟶AR ⟶RZ ◅ ε

⟶⋆-≈cong∙ : ∀ {α β} {x₁ x₂ : Tm (α ⇒ β)} {y₁ y₂ : Tm α} →
             x₁ ⟶⋆ x₂ → y₁ ⟶⋆ y₂ → x₁ ∙ y₁ ⟶⋆ x₂ ∙ y₂
⟶⋆-≈cong∙ x₁⟶⋆x₂ y₁⟶⋆y₂ =
  gmap (flip _∙_ _) ⟶AL x₁⟶⋆x₂
    ◅◅ gmap (_∙_ _) ⟶AR y₁⟶⋆y₂

--
-- _⟶⋆_ implies _≈_ .
--

mutual

  ⟶→≈ : ∀ {α} {x y : Tm α} → x ⟶ y → x ≈ y

  ⟶→≈ ⟶K = ≈K
  ⟶→≈ ⟶S = ≈S
  ⟶→≈ (⟶AL x⟶y) = ≈cong∙ (⟶→≈ x⟶y) ≈refl
  ⟶→≈ (⟶AR x⟶y) = ≈cong∙ ≈refl (⟶→≈ x⟶y)
  ⟶→≈ ⟶RZ = ≈RZ
  ⟶→≈ ⟶RS = ≈RS

  ⟶⋆→≈ : ∀ {α} {x y : Tm α} → x ⟶⋆ y → x ≈ y

  ⟶⋆→≈ ε = ≈refl
  ⟶⋆→≈ (x⟶x′ ◅ x′⟶⋆y) = ≈trans (⟶→≈ x⟶x′) (⟶⋆→≈ x′⟶⋆y)

RH : {α : Ty} (p : G α) → Set
RH {N} p = ⊤
RH {α ⇒ β} p = ∀ (q : G α) → RH q →
  ⟪ p ⟫ ∙ ⟪ q ⟫ ⟶⋆ ⟪ p ⟨∙⟩ q ⟫
    × RH (p ⟨∙⟩ q)

-- "Application" for RH-values.

||∙|| : ∀ {α β}
  (p : G (α ⇒ β)) (f : RH p) (q : G α) (g : RH q) → RH (p ⟨∙⟩ q)
||∙|| p f q g = proj₂ (f q g)

-- all-RH-R∙

all-RH-R∙ : ∀ {α} (p : G α) (f : RH p)
  (q : G (N ⇒ α ⇒ α)) (g : RH q) (n : ℕ) →
    RH (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ n)

all-RH-R∙ p f q g zero =
  RH p ∋ f

all-RH-R∙ p f q g (suc m) =
  RH (q ⟨∙⟩ m ⟨∙⟩ (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m))
    ∋ ||∙|| (q ⟨∙⟩ m) (||∙|| q g m tt) (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m)
            (all-RH-R∙ p f q g m)

-- all-RH-R⟶⋆

all-RH-R⟶⋆ : ∀ {α} (p : G α) (f : RH p)
  (q : G (N ⇒ α ⇒ α)) (g : RH q) (m : ℕ) →
    ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ m ⟫ ⟶⋆ ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫

all-RH-R⟶⋆ p f q g zero = begin
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ zero ⟫
    ≡⟨ refl ⟩
  REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ZERO
    ⟶⟨ ⟶RZ ⟩
  ⟪ p ⟫
    ≡⟨ refl ⟩
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ zero ⟫
  ∎
  where open StarReasoning _⟶_

all-RH-R⟶⋆ p f q g (suc m) = begin
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ suc m ⟫
    ≡⟨ refl ⟩
  REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ (SUC ∙ ⟪ m ⟫)
    ⟶⟨ ⟶RS ⟩
  (⟪ q ⟫ ∙ ⟪ m ⟫) ∙ (REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ m ⟫)
    ⟶⋆⟨ ⟶⋆-≈cong∙ (proj₁ $ g m tt) (all-RH-R⟶⋆ p f q g m) ⟩
  ⟪ (q ⟨∙⟩ m) ⟫ ∙ ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫
    ⟶⋆⟨ proj₁ $ (||∙|| q g m tt)
                       (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) (all-RH-R∙ p f q g m) ⟩
  ⟪ (q ⟨∙⟩ m) ⟨∙⟩ (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) ⟫
    ≡⟨ refl ⟩
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ suc m ⟫
  ∎  
  where open StarReasoning _⟶_

--
-- Any G-value produced from a term is an RH-value!
--

all-RH : ∀ {α} (x : Tm α) → RH ⟦ x ⟧

all-RH K p f =
  ε , λ q g →
    ⟶K ◅ ε , f

all-RH S p f =
  ε , (λ q g →
    ε , (λ r h →
      (begin
        S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫
          ⟶⟨ ⟶S ⟩
        (⟪ p ⟫ ∙ ⟪ r ⟫) ∙ (⟪ q ⟫ ∙ ⟪ r ⟫)
          ⟶⋆⟨ ⟶⋆-≈cong∙ (proj₁ $ f r h) (proj₁ $ g r h) ⟩
        ⟪ p ⟨∙⟩ r ⟫ ∙ ⟪ q ⟨∙⟩ r ⟫
          ⟶⋆⟨ proj₁ $ (||∙|| p f r h) (q ⟨∙⟩ r) (||∙|| q g r h) ⟩
        ⟪ (p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r) ⟫
      ∎)
      ,
      ||∙|| (p ⟨∙⟩ r) (||∙|| p f r h)
            (q ⟨∙⟩ r) (||∙|| q g r h)))
  where open StarReasoning _⟶_

all-RH (x ∙ y) =
  ||∙|| ⟦ x ⟧ (all-RH x) ⟦ y ⟧ (all-RH y)

all-RH ZERO =
  tt

all-RH SUC p f =
  ε , tt

all-RH REC p f =
  ε , λ q g →
    ε , λ n r →
      all-RH-R⟶⋆ p f q g n , all-RH-R∙ p f q g n

--
-- x ⟶⋆ norm x
--

⟶⋆norm : ∀ {α} (x : Tm α) → x ⟶⋆ norm x

⟶⋆norm K = ε
⟶⋆norm S = ε
⟶⋆norm (x ∙ y) = begin
  x ∙ y
    ⟶⋆⟨ ⟶⋆-≈cong∙ (⟶⋆norm x) (⟶⋆norm y) ⟩
  norm x ∙ norm y
    ≡⟨ refl ⟩
  ⟪ ⟦ x ⟧ ⟫ ∙ ⟪ ⟦ y ⟧ ⟫
    ⟶⋆⟨ proj₁ $ all-RH x ⟦ y ⟧ (all-RH y) ⟩
  ⟪ ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧ ⟫
    ≡⟨ refl ⟩
  norm (x ∙ y)
  ∎
  where open StarReasoning _⟶_
⟶⋆norm ZERO = ε
⟶⋆norm SUC = ε
⟶⋆norm REC = ε

--
-- Church-Rosser:
--     x ⟶⋆ y′  →  x ⟶⋆ y′′  →  ∃ λ y → y′ ⟶⋆ y × y′′ ⟶⋆ y
--

confluence : ∀ {α} {x y′ y′′ : Tm α} →
  x ⟶⋆ y′  →  x ⟶⋆ y′′  →  ∃ λ y → y′ ⟶⋆ y × y′′ ⟶⋆ y
confluence {α} {x} {y′} {y′′} x⟶⋆y′ x⟶⋆y′′ =
  norm y′ , (⟶⋆norm y′) , subst (_⟶⋆_ y′′) ny′′≡ny′ (⟶⋆norm y′′)
  where

  y′′≈y′ : y′′ ≈ y′
  y′′≈y′ = begin
    y′′
      ≈⟨ ≈sym $ ⟶⋆→≈ x⟶⋆y′′ ⟩
    x
      ≈⟨ ⟶⋆→≈ x⟶⋆y′ ⟩
    y′
    ∎ where open ≈-Reasoning

  ny′′≡ny′ : norm y′′ ≡ norm y′
  ny′′≡ny′ = norm-sound y′′≈y′
