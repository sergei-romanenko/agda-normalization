module STLC-Delay.DelayMonad where

import Relation.Binary.EqReasoning as EqReasoning

open import STLC-Delay.Utils

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

-- Map for ∞Delay

infixl 4 _∞<$>_

_∞<$>_ : ∀ {A B i} (f : A → B) (∞a : ∞Delay i A) → ∞Delay i B
f ∞<$> ∞a = ∞a ∞>>= (now ∘ f)

-- force (f ∞<$> ∞a) = f <$> force ∞a

--
-- Strong bisimilarity.
--

infix 4 _~_ _~⟨_⟩~_ _∞~⟨_⟩~_ _∞~_

mutual

  data _~_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
    ~now   : ∀ a → now a ~ now a
    ~later : ∀ {a∞ b∞} (a∞~b∞ : a∞ ∞~⟨ i ⟩~ b∞) → later a∞ ~ later b∞

  _~⟨_⟩~_ = λ {A} a? i b? → _~_ {i} {A} a? b?


  record _∞~⟨_⟩~_ {A} (a∞ : ∞Delay ∞ A) (i : Size) (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ~force : {j : Size< i} → force a∞ ~⟨ j ⟩~ force b∞

  _∞~_ = λ {i : Size} {A : Set} a∞ b∞ → _∞~⟨_⟩~_ {A} a∞ i b∞

open _∞~⟨_⟩~_ public

-- a? ~⟨ i ⟩~ a?

mutual

  ~refl : ∀ {A i} (a? : Delay ∞ A) → a? ~⟨ i ⟩~ a?
  ~refl (now a) = ~now a
  ~refl (later a∞) = ~later (∞~refl a∞)

  ∞~refl : ∀ {A i} (a∞ : ∞Delay ∞ A) → a∞ ∞~⟨ i ⟩~ a∞
  ~force (∞~refl a∞) = ~refl (force a∞)

-- a? ~⟨ i ⟩~ b? → b? ~⟨ i ⟩~ a?

mutual

  ~sym : ∀ {A i} {a? b? : Delay ∞ A} →
    a? ~⟨ i ⟩~ b? → b? ~⟨ i ⟩~ a?
  ~sym (~now a) = ~now a
  ~sym (~later a∞~b∞) = ~later (∞~sym a∞~b∞)

  ∞~sym : ∀ {A i} {a∞ b∞ : ∞Delay ∞ A} →
    a∞ ∞~⟨ i ⟩~ b∞ → b∞ ∞~⟨ i ⟩~ a∞
  ~force (∞~sym a∞∞~b∞) = ~sym (~force a∞∞~b∞)

-- a? ~⟨ i ⟩~ b? → b? ~⟨ i ⟩~ c? → a? ~⟨ i ⟩~ c?

mutual

  ~trans :  ∀ {A i} {a? b? c? : Delay ∞ A} →
    a? ~⟨ i ⟩~ b? → b? ~⟨ i ⟩~ c? → a? ~⟨ i ⟩~ c?
  ~trans (~now a) (~now .a) = ~now a
  ~trans (~later a∞~b∞) (~later b∞~c∞) = ~later (∞~trans a∞~b∞ b∞~c∞)

  ∞~trans : ∀ {A i} {a∞ b∞ c∞ : ∞Delay ∞ A} →
    a∞ ∞~⟨ i ⟩~ b∞ → b∞ ∞~⟨ i ⟩~ c∞ → a∞ ∞~⟨ i ⟩~ c∞
  ~force (∞~trans a∞∞~b∞ b∞∞~c∞) = ~trans (~force a∞∞~b∞) (~force b∞∞~c∞)

-- ~-Reasoning

~setoid : {A : Set} {i : Size} → Setoid lzero lzero

~setoid {A} {i} = record
  { Carrier = Delay ∞ A
  ; _≈_ = _~_ {i} {A}
  ; isEquivalence = record
    { refl = ~refl _
    ; sym = ~sym
    ; trans = ~trans } }

module ~-Reasoning {A : Set} {i : Size} = EqReasoning (~setoid {A} {i})

-- ∞~-Reasoning

∞~setoid : {A : Set} {i : Size} → Setoid lzero lzero

∞~setoid {A} {i} = record
  { Carrier = ∞Delay ∞ A
  ; _≈_ = _∞~_ {i} {A}
  ; isEquivalence = record
    { refl = ∞~refl _
    ; sym = ∞~sym
    ; trans = ∞~trans } }

module ∞~-Reasoning {A : Set} {i : Size} = EqReasoning (∞~setoid {A} {i})

--
-- Delay monad laws.
--

mutual

  bind-assoc : ∀ {A B C i} {f : A → Delay ∞ B} {g : B → Delay ∞ C}
    (a? : Delay ∞ A) →
    ((a? >>= f) >>= g) ~⟨ i ⟩~ (a? >>= λ a → (f a >>= g))
  bind-assoc (now a) = ~refl _
  bind-assoc (later a∞) = ~later (∞bind-assoc a∞)

  ∞bind-assoc : ∀ {A B C i} {f : A → Delay ∞ B} {g : B → Delay ∞ C}
    (a∞ : ∞Delay ∞ A) →
    ((a∞ ∞>>= f) ∞>>= g) ∞~⟨ i ⟩~ (a∞ ∞>>= λ a → (f a >>= g))
  ~force (∞bind-assoc a∞) = bind-assoc (force a∞)

mutual

  bind-cong-l : ∀ {A B i} {a? b? : Delay ∞ A}
    (a?~b? : a? ~⟨ i ⟩~ b?) (f : A → Delay ∞ B) →
    (a? >>= f) ~⟨ i ⟩~ (b? >>= f)
  bind-cong-l (~now a) f = ~refl (f a)
  bind-cong-l (~later a∞~b∞) f = ~later (∞bind-cong-l a∞~b∞ f)

  ∞bind-cong-l : ∀ {A B i} {a∞ b∞ : ∞Delay ∞ A}
    (a∞∞~b∞ :  a∞ ∞~⟨ i ⟩~ b∞) (f : A → Delay ∞ B) →
    (a∞ ∞>>= f) ∞~⟨ i ⟩~ (b∞ ∞>>= f)
  ~force (∞bind-cong-l a∞∞~b∞ f) = bind-cong-l (~force a∞∞~b∞) f

mutual

  bind-cong-r : ∀ {A B i} (a? : Delay ∞ A)
    {f g : A → Delay ∞ B} (f~g : ∀ a → f a ~⟨ i ⟩~ g a) →
    (a? >>= f) ~⟨ i ⟩~ (a? >>= g)
  bind-cong-r (now a) f~g = f~g a
  bind-cong-r (later a∞) f~g = ~later (∞bind-cong-r a∞ f~g)

  ∞bind-cong-r : ∀ {A B i} (a∞ : ∞Delay ∞ A)
    {f g : A → Delay ∞ B} (f~g : ∀ a → f a ~⟨ i ⟩~ g a) →
    (a∞ ∞>>= f) ∞~⟨ i ⟩~ (a∞ ∞>>= g)
  ~force (∞bind-cong-r a∞ f~g) = bind-cong-r (force a∞) f~g

bind-cong :  ∀ {A B i} {a? b? : Delay ∞ A} {f g : A → Delay ∞ B} →
  a? ~⟨ i ⟩~ b? → (∀ a → f a ~⟨ i ⟩~ g a) →
  (a? >>= f) ~⟨ i ⟩~ (b? >>= g)
bind-cong {A} {B} {i} {a?} {b?} {f} {g} a?~b? f~g = begin
  (a? >>= f)
    ≈⟨ bind-cong-l a?~b? f ⟩
  (b? >>= f)
    ≈⟨ bind-cong-r b? f~g ⟩
  (b? >>= g)
  ∎
  where open ~-Reasoning


map-compose : ∀{A B C i} {f : A → B} {g : B → C} (a? : Delay ∞ A) →
  (g <$> (f <$> a?)) ~⟨ i ⟩~ ((g ∘ f) <$> a?)
map-compose a? = bind-assoc a?

map-cong : ∀{A B i} (f : A → B) {a? b? : Delay ∞ A} →
  a? ~⟨ i ⟩~ b? → (f <$> a?) ~⟨ i ⟩~ (f <$> b?)
map-cong f a?~b? = bind-cong-l a?~b? (now ∘ f)


--
-- Termination/Convergence. Makes sense only for Delay ∞ A.
--

infix 4 _⇓_

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Substitution.

subst~⇓ : ∀ {A} {a? b? : Delay ∞ A} (a?~b? : a? ~ b?)
  {a : A} (⇓a : a? ⇓ a) → b? ⇓ a
subst~⇓ (~now a) now⇓ = now⇓
subst~⇓ (~later a∞~b∞) (later⇓ ⇓a) =
  later⇓ (subst~⇓ (~force a∞~b∞) ⇓a)

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

⇓bind2 : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C} (⇓fab : (a? >>= (λ a → b? >>= f a)) ⇓ fab) → f a b ⇓ fab
⇓bind2 f now⇓ now⇓ ⇓fab = ⇓fab
⇓bind2 f now⇓ (later⇓ ⇓b) (later⇓ ⇓fab) = ⇓bind2 f now⇓ ⇓b ⇓fab
⇓bind2 f (later⇓ ⇓a) ⇓b (later⇓ ⇓fab) = ⇓bind2 f ⇓a ⇓b ⇓fab

bind⇓ : ∀ {A B} (f : A → Delay ∞ B)
  {a? a} (⇓a : a? ⇓ a) {fa} (⇓fa : f a ⇓ fa) →
  (a? >>= f) ⇓ fa
bind⇓ f now⇓ ⇓fa = ⇓fa
bind⇓ f (later⇓ ⇓a) ⇓fa = later⇓ (bind⇓ f ⇓a ⇓fa)

bind2⇓ : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C}  (⇓fab : f a b ⇓ fab) →
  (a? >>= (λ a → b? >>= f a)) ⇓ fab
bind2⇓ f now⇓ now⇓ ⇓fab = ⇓fab
bind2⇓ f now⇓ (later⇓ ⇓b) ⇓fab = later⇓ (bind2⇓ f now⇓ ⇓b ⇓fab)
bind2⇓ f (later⇓ ⇓a) ⇓b ⇓fab = later⇓ (bind2⇓ f ⇓a ⇓b ⇓fab)

--
-- Determinism: a? ⇓ a₁ → a? ⇓ a₂ → a₁ ≡ a₁
-- 

⇓-det : ∀ {A} {a? : Delay ∞ A}
  {a₁} (⇓a₁ : a? ⇓ a₁) {a₂} (⇓a₂ : a? ⇓ a₂) → 
  a₁ ≡ a₂
⇓-det now⇓ now⇓ = refl
⇓-det (later⇓ ⇓a₁) (later⇓ ⇓a₂) = ⇓-det ⇓a₁ ⇓a₂

