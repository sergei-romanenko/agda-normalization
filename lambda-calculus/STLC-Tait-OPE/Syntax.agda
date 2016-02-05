module STLC-Tait-OPE.Syntax where

import Relation.Binary.EqReasoning as EqReasoning

open import STLC-Tait-OPE.Util


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
    _⊙_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ) (σ′ : Sub Γ′ Δ) → Sub Γ′ Γ
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
-- A "denotational" semantics for `Tm α`.
--

module DenotationalEval where

  D : (α : Ty) → Set
  D ⋆ = ⊤
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

    ⟦_⟧*_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ′) (ρ : DEnv Γ Δ) → DEnv Γ Γ′
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
-- Convertibility.
--

infix 4 _≈_ _≈≈_

mutual

  -- σ₁ ≈≈ σ₂

  data _≈≈_ : ∀ {Γ Δ} (σ₁ σ₂ : Sub Γ Δ) → Set where
    ≈≈refl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ≈≈ σ
    ≈≈sym : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} →
      σ₁ ≈≈ σ₂ → σ₂ ≈≈ σ₁
    ≈≈trans : ∀ {Γ Δ} {σ₁ σ₂ σ₃ : Sub Γ Δ} →
      σ₁ ≈≈ σ₂ → σ₂ ≈≈ σ₃ → σ₁ ≈≈ σ₃
    ≈≈cong⊙ : ∀ {Γ Δ Γ′} {σ₁ σ₂ : Sub Δ Γ} {τ₁ τ₂ : Sub Γ′ Δ} →
      σ₁ ≈≈ σ₂ → τ₁ ≈≈ τ₂ → σ₁ ⊙ τ₁ ≈≈ σ₂ ⊙ τ₂
    ≈≈cong∷ : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α} {σ₁ σ₂ : Sub Δ Γ} →
      t₁ ≈ t₂ → σ₁ ≈≈ σ₂ → t₁ ∷ σ₁ ≈≈ t₂ ∷ σ₂
    ≈≈assoc : ∀ {Γ Δ Δ′ Γ′} {σ₁ : Sub Δ Γ} {σ₂ : Sub Δ′ Δ} {σ₃ : Sub Γ′ Δ′} →
      (σ₁ ⊙ σ₂) ⊙ σ₃ ≈≈ σ₁ ⊙ (σ₂ ⊙ σ₃)
    ≈≈idl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      ı ⊙ σ ≈≈ σ
    ≈≈idr : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ⊙ ı ≈≈ σ
    ≈≈wk : ∀ {α Γ Δ} {σ : Sub Γ Δ} {t : Tm Γ α} →
      ↑ ⊙ (t ∷ σ) ≈≈ σ
    ≈≈cons : ∀ {α Γ Δ Γ′} {σ : Sub Δ Γ} {t : Tm Δ α} {σ′ : Sub Γ′ Δ} →
      (t ∷ σ) ⊙ σ′ ≈≈ t [ σ′ ] ∷ (σ ⊙ σ′)
    ≈≈id∷ : ∀ {α Γ} →
      ı {α ∷ Γ} ≈≈ ø ∷ (ı ⊙ ↑)

  -- t₁ ≈ t₂

  data _≈_  : ∀ {α Γ} (t₁ t₂ : Tm Γ α) → Set where
    ≈refl : ∀ {α Γ} {t : Tm Γ α} →
      t ≈ t
    ≈sym : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₁
    ≈trans : ∀ {α Γ} {t₁ t₂ t₃ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
    ≈cong∙ : ∀ {α β Γ} {f₁ f₂ : Tm Γ (α ⇒ β)} {t₁ t₂ : Tm Γ α} →
      f₁ ≈ f₂ → t₁ ≈ t₂ → f₁ ∙ t₁ ≈ f₂ ∙ t₂
    ≈cong[] : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α } {σ₁ σ₂ : Sub Γ Δ} →
      t₁ ≈ t₂ → σ₁ ≈≈ σ₂ → t₁ [ σ₁ ] ≈ t₂ [ σ₂ ]
    ≈congƛ : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
      t₁ ≈ t₂ → (ƛ t₁) ≈ (ƛ t₂)
    ≈proj : ∀ {α Γ Δ} {t : Tm Γ α } {σ : Sub Γ Δ} →
      ø [ t ∷ σ ] ≈ t
    ≈id : ∀ {α Γ} {t : Tm Γ α} →
      t [ ı ] ≈ t
    ≈comp : ∀ {α Γ Δ Γ′} {t : Tm Δ α} {σ : Sub Γ Δ} {σ′ : Sub Γ′ Γ} →
      t [ σ ⊙ σ′ ] ≈ t [ σ ] [ σ′ ]
    ≈lam : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} →
      (ƛ t) [ σ ] ≈ (ƛ t [ ø ∷ (σ ⊙ ↑) ])
    ≈app : ∀ {α β Γ Δ} {f : Tm Δ (α ⇒ β)} {t : Tm Δ α} {σ : Sub Γ Δ} →
      (f ∙ t) [ σ ] ≈ f [ σ ] ∙ t [ σ ]
    ≈βσ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} {t′ : Tm Γ α} →
      (ƛ t) [ σ ] ∙ t′ ≈ t [ t′ ∷ σ ]
    ≈η : ∀ {α β Γ} {t : Tm Γ (α ⇒ β)} →
      t ≈ (ƛ (t [ ↑ ] ∙ ø))

-- ≈≈-Reasoning

≈≈setoid : {Γ Δ : Ctx} → Setoid _ _

≈≈setoid {Γ} {Δ} = record
  { Carrier = Sub Γ Δ
  ; _≈_ = _≈≈_
  ; isEquivalence = record
    { refl = ≈≈refl
    ; sym = ≈≈sym
    ; trans = ≈≈trans } }

module ≈≈-Reasoning {Γ} {Δ} = EqReasoning (≈≈setoid {Γ} {Δ})

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
-- Weak head normal forms.
--

data Var : Ctx → Ty → Set where
  zero : ∀ {α Γ} → Var (α ∷ Γ) α
  suc  : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

mutual

  data Val : Ctx → Ty → Set where
    ne  : ∀ {α Γ} (us : NeVal Γ α) → Val Γ α
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → Val Γ (α ⇒ β)

  data Env (Γ : Ctx) : Ctx → Set where
    []  : Env Γ []
    _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)

  data NeVal (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeVal Γ α
    app : ∀ {α β} (us : NeVal Γ (α ⇒ β)) (u : Val Γ α) → NeVal Γ β


--
-- η-long β-normal forms.
--

mutual

  data Nf (Γ : Ctx) : Ty → Set where
    ne  : ∀ (ns : NeNf Γ ⋆) → Nf Γ ⋆
    lam : ∀ {α β} (n : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)

  data NeNf (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeNf Γ α
    app : ∀ {α β} (ns : NeNf Γ (α ⇒ β)) (n : Nf Γ α) → NeNf Γ β


--
-- Embedding of values and normal forms into terms.
--

embVar : ∀ {α Γ} (x : Var Γ α) → Tm Γ α
embVar zero = ø
embVar (suc x) = embVar x [ ↑ ]

sub-from-[] : ∀ {Γ} → Sub Γ []
sub-from-[] {[]} = ı
sub-from-[] {α ∷ Γ} = sub-from-[] ⊙ ↑

mutual

  embNeVal : ∀ {α Γ} (us : NeVal Γ α) → Tm Γ α
  embNeVal (var x) = embVar x
  embNeVal (app us u) = embNeVal us ∙ embVal u

  embVal : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  embVal (lam t ρ) =
    (ƛ t) [ embEnv ρ ]
  embVal (ne us) = embNeVal us

  embEnv : ∀ {Γ Δ} (ρ : Env Γ Δ) → Sub Γ Δ
  embEnv [] = sub-from-[]
  embEnv (u ∷ ρ) = embVal u ∷ embEnv ρ

mutual

  embNeNf : ∀ {α Γ} (ns : NeNf Γ α) → Tm Γ α
  embNeNf (var x) = embVar x
  embNeNf (app ns n) = embNeNf ns ∙ embNf n

  embNf : ∀ {α Γ} (n : Nf Γ α) → Tm Γ α
  embNf (lam n) = ƛ embNf n
  embNf (ne ns) = embNeNf ns


--
-- Weakening contexts by means of order preserving embeddings.
--

infix 4 _≤_

data _≤_ : (Γ Δ : Ctx) → Set where
  ≤[]   : [] ≤ []
  ≤weak : ∀ {α Γ Δ} (η : Γ ≤ Δ) → α ∷ Γ ≤ Δ
  ≤lift : ∀ {α Γ Δ} (η : Γ ≤ Δ) → α ∷ Γ ≤ α ∷ Δ

≤id : ∀ {Γ} → Γ ≤ Γ
≤id {[]} = ≤[]
≤id {α ∷ Γ} = ≤lift ≤id

infixr 6 _●_

_●_ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (η′ : Γ ≤ Δ) → Β ≤ Δ
≤[] ● ≤[] = ≤[]
≤weak η ● η′ = ≤weak (η ● η′)
≤lift η ● ≤weak η′ = ≤weak (η ● η′)
≤lift η ● ≤lift η′ = ≤lift (η ● η′)

≤id●η :  ∀ {Γ Δ} (η : Γ ≤ Δ) → ≤id ● η ≡ η
≤id●η ≤[] = refl
≤id●η (≤weak η) = cong ≤weak (≤id●η η)
≤id●η (≤lift η) = cong ≤lift (≤id●η η)

η●≤id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η ● ≤id ≡ η
η●≤id ≤[] = refl
η●≤id (≤weak η) = cong ≤weak (η●≤id η)
η●≤id (≤lift η) = cong ≤lift (η●≤id η)

assoc● :  ∀ {Β Γ₁ Γ₂ Δ} (η : Β ≤ Γ₁) (η′ : Γ₁ ≤ Γ₂) (η′′ : Γ₂ ≤ Δ) →
  (η ● η′) ● η′′ ≡ η ● (η′ ● η′′)
assoc● ≤[] ≤[] ≤[] = refl
assoc● (≤weak η) η′ η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤weak η′) η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤weak η′′) = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤lift η′′) = cong ≤lift (assoc● η η′ η′′)

--
-- Applying OPEs.
--

var≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (x : Var Δ α) → Var Γ α
var≤ ≤[] x = x
var≤ (≤weak η) x = suc (var≤ η x)
var≤ (≤lift η) zero = zero
var≤ (≤lift η) (suc x) = suc (var≤ η x)

mutual

  val≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (u : Val Δ α) → Val Γ α
  val≤ η (ne us) = ne (neVal≤ η us)
  val≤ η (lam t ρ) = lam t (env≤ η ρ)

  neVal≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (us : NeVal Δ α) → NeVal Γ α
  neVal≤ η (var x) = var (var≤ η x)
  neVal≤ η (app us u) = app (neVal≤ η us) (val≤ η u)

  env≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ρ : Env Δ α) → Env Γ α
  env≤ η [] = []
  env≤ η (u ∷ ρ) = val≤ η u ∷ env≤ η ρ

  nf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (n : Nf Δ α) → Nf Γ α
  nf≤ η (ne ns) = ne (neNf≤ η ns)
  nf≤ η (lam n) = lam (nf≤ (≤lift η) n)

  neNf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ns : NeNf Δ α) → NeNf Γ α
  neNf≤ η (var x) = var (var≤ η x)
  neNf≤ η (app ns n) = app (neNf≤ η ns) (nf≤ η n)

--
-- ≤ to Sub.
--

sub≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) → Sub Γ Δ
sub≤ ≤[] = ı
sub≤ (≤weak η) = sub≤ η ⊙ ↑
sub≤ (≤lift η) = ø ∷ sub≤ η ⊙ ↑

--
-- Applying ≤id.
--

var≤∘≤id : ∀ {α Γ} (x : Var Γ α) → var≤ ≤id x ≡ x
var≤∘≤id zero = refl
var≤∘≤id (suc x) = cong suc (var≤∘≤id x)

mutual

  val≤∘≤id : ∀ {α Γ} (u : Val Γ α) → val≤ ≤id u ≡ u
  val≤∘≤id (ne us) = cong ne (neVal≤∘≤id us)
  val≤∘≤id (lam t ρ) = cong (lam t) (env≤∘≤id ρ)

  neVal≤∘≤id : ∀ {α Γ} (us : NeVal Γ α) → neVal≤ ≤id us ≡ us
  neVal≤∘≤id (var x) = cong var (var≤∘≤id x)
  neVal≤∘≤id (app us u) = cong₂ app (neVal≤∘≤id us) (val≤∘≤id u)

  env≤∘≤id : ∀ {Γ Δ} (ρ : Env Δ Γ) → env≤ ≤id ρ ≡ ρ
  env≤∘≤id [] = refl
  env≤∘≤id (u ∷ ρ) = cong₂ _∷_ (val≤∘≤id u) (env≤∘≤id ρ)

  nf≤∘≤id : ∀ {α Γ} (n : Nf Γ α) → nf≤ ≤id n ≡ n
  nf≤∘≤id (ne ns) = cong ne (neNf≤∘≤id ns)
  nf≤∘≤id (lam n) = cong lam (nf≤∘≤id n)

  neNf≤∘≤id : ∀ {α Γ} (ns : NeNf Γ α) → neNf≤ ≤id ns ≡ ns
  neNf≤∘≤id (var x) = cong var (var≤∘≤id x)
  neNf≤∘≤id (app ns u) = cong₂ app (neNf≤∘≤id ns) (nf≤∘≤id u)

--
-- sub≤ ≤id ≈≈ ı
--

ı≈≈sub≤-≤id : ∀ {Γ} → sub≤ {Γ} ≤id ≈≈ ı
ı≈≈sub≤-≤id {[]} = ≈≈refl
ı≈≈sub≤-≤id {α ∷ Γ} = begin
  ø ∷ sub≤ ≤id ⊙ ↑
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong⊙ ı≈≈sub≤-≤id ≈≈refl) ⟩
  ø ∷ ı ⊙ ↑
    ≈⟨ ≈≈sym ≈≈id∷ ⟩
  ı
  ∎
  where open ≈≈-Reasoning

--
-- Weakening
--

wk : ∀ {α Γ} → α ∷ Γ ≤ Γ
wk = ≤weak ≤id

--
-- Identity environments.
--

id-env : ∀ {Γ} → Env Γ Γ
id-env {[]} = []
id-env {α ∷ Γ} = ne (var zero) ∷ env≤ wk id-env

--
-- Relational big-step semantics.
--

mutual

  infix 4 ⟦_⟧_⇓_ ⟦_⟧*_⇓_ _⟨∙⟩_⇓_

  data ⟦_⟧_⇓_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (u : Val Γ α) → Set where
    ø⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ø ⟧ (u ∷ ρ) ⇓ u
    ∙⇓ : ∀ {α β Γ Δ} {t : Tm Δ (α ⇒ β)} {t′ : Tm Δ α} {ρ : Env Γ Δ} {u v w}
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓v : ⟦ t′ ⟧ ρ ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w) →
      ⟦ t ∙ t′ ⟧ ρ ⇓ w
    ƛ⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} →
      ⟦ ƛ t ⟧ ρ ⇓ lam t ρ
    []⇓ : ∀ {α Γ Δ Δ′} {t : Tm Δ′ α } {σ : Sub Δ Δ′} {ρ : Env Γ Δ} {θ u}
      (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) (⇓u : ⟦ t ⟧ θ ⇓ u) →
      ⟦ t [ σ ] ⟧ ρ ⇓ u

  data ⟦_⟧*_⇓_ : ∀ {Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) (θ : Env Γ Δ′) →
       Set where
    ι⇓ : ∀ {Γ Σ} {ρ : Env Γ Σ} →
      ⟦ ı ⟧* ρ ⇓ ρ
    ⊙⇓ : ∀ {Γ Δ Δ′ Δ′′} {σ : Sub Δ′ Δ′′} {σ′ : Sub Δ Δ′} {ρ : Env Γ Δ} {θ₁ θ₂}
      (⇓θ₁ : ⟦ σ′ ⟧* ρ ⇓ θ₁) (⇓θ₂ : ⟦ σ ⟧* θ₁ ⇓ θ₂) →
      ⟦ σ ⊙ σ′ ⟧* ρ ⇓ θ₂
    ∷⇓ : ∀ {α Γ Δ Δ′} {t : Tm Δ α} {σ : Sub Δ Δ′} {ρ : Env Γ Δ} {u θ}
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) →
      ⟦ t ∷ σ ⟧* ρ ⇓ (u ∷ θ)
    ↑⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ↑ ⟧* (u ∷ ρ) ⇓ ρ

  data _⟨∙⟩_⇓_ : ∀ {α β Γ}
       (u : Val Γ (α ⇒ β)) (v : Val Γ α) (w : Val Γ β) → Set where
    ne⇓  : ∀ {α β Γ} {us : NeVal Γ (α ⇒ β)} {u} →
      ne us ⟨∙⟩ u ⇓ ne (app us u)
    lam⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} {u v}
      (⇓v : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v

mutual

  data Quote_⇓_ : ∀ {α Γ} (u : Val Γ α) (n : Nf Γ α) → Set where
    ⋆⇓ : ∀ {Γ} (us : NeVal Γ ⋆) {ns}
      (⇓ns : Quote* us ⇓ ns) →
      Quote (ne us) ⇓ ne ns
    ⇒⇓ : ∀ {α β Γ} {f : Val Γ (α ⇒ β)} {u n} →
      (⇓u : val≤ wk f ⟨∙⟩ ne (var zero) ⇓ u) (⇓n : Quote u ⇓ n) →
      Quote f ⇓ lam n

  data Quote*_⇓_ : ∀ {α Γ} (us : NeVal Γ α) (ns : NeNf Γ α) → Set where
    var⇓ : ∀ {α Γ} {x : Var Γ α} →
      Quote* var x ⇓ var x
    app⇓ : ∀ {α β Γ} {us : NeVal Γ (α ⇒ β)} {u : Val Γ α} {ns n}
      (⇓ns : Quote* us ⇓ ns) (⇓n : Quote u ⇓ n) →
      Quote* app us u ⇓ app ns n


data Nf_⇓_ : ∀ {α Γ} (t : Tm Γ α) (n : Nf Γ α) → Set where
  nf⇓ : ∀ {α Γ} {t : Tm Γ α} {u n}
    (⇓u : ⟦ t ⟧ id-env ⇓ u) (⇓n : Quote u ⇓ n) →
    Nf t ⇓ n

nf-III⇓ : Nf III ⇓ lam (ne (var zero))
nf-III⇓ = nf⇓ (∙⇓ ƛ⇓ (∙⇓ ƛ⇓ ƛ⇓ (lam⇓ ø⇓)) (lam⇓ ø⇓))
                  (⇒⇓ (lam⇓ ø⇓) (⋆⇓ (var zero) var⇓))

--
-- Determinism (left-injectivity) of ⟦_⟧_⇓_ , Quote_⇓_ and Nf_⇓_ :
--
--   ⟦ t ⟧ ρ₁ ⇓ u₁ →  ⟦ t ⟧ ρ₂ ⇓ u₂ → ρ₁ ≡ ρ₂ → u₁ ≡ u₂
--   Quote u₁ ⇓ n₁ →  Quote u₂ ⇓ n₂ → u₁ ≡ u₂ →  n₁ ≡ n₂
--   Nf t ⇓ n₁ → Nf t ⇓ n₂ → n₁ ≡ n₂
--

--   ⟦ t ⟧ ρ₁ ⇓ u₁ →  ⟦ t ⟧ ρ₂ ⇓ u₂ → ρ₁ ≡ ρ₂ → u₁ ≡ u₂

mutual

  ⟦⟧⇓-det : ∀ {α Γ Δ} {t : Tm Δ α} {ρ₁ ρ₂ : Env Γ Δ} {u₁ u₂} →
    (⇓u₁ : ⟦ t ⟧ ρ₁ ⇓ u₁) (⇓u₂ : ⟦ t ⟧ ρ₂ ⇓ u₂)
    (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂) → u₁ ≡ u₂

  ⟦⟧⇓-det ø⇓ ø⇓ refl = refl
  ⟦⟧⇓-det (∙⇓ ⇓u₁ ⇓v₁ ⇓w₁) (∙⇓ ⇓u₂ ⇓v₂ ⇓w₂) ρ₁≡ρ₂ =
    ⟨∙⟩⇓-det ⇓w₁ ⇓w₂ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧⇓-det ⇓v₁ ⇓v₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det ƛ⇓ ƛ⇓ refl = refl
  ⟦⟧⇓-det ([]⇓ ⇓ρ₁ ⇓u₁) ([]⇓ ⇓ρ₂ ⇓u₂) ρ₁≡ρ₂ =
    ⟦⟧⇓-det ⇓u₁ ⇓u₂ (⟦⟧*⇓-det ⇓ρ₁ ⇓ρ₂ ρ₁≡ρ₂)

  ⟦⟧*⇓-det : ∀ {Γ Δ Δ′} {σ : Sub Δ Δ′} {ρ₁ ρ₂ : Env Γ Δ} {θ₁ θ₂}
    (⇓θ₁ : ⟦ σ ⟧* ρ₁ ⇓ θ₁) (⇓θ₂ : ⟦ σ ⟧* ρ₂ ⇓ θ₂)
    (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂) → θ₁ ≡ θ₂

  ⟦⟧*⇓-det ι⇓ ι⇓ ρ₁≡ρ₂ = ρ₁≡ρ₂
  ⟦⟧*⇓-det (⊙⇓ ⇓θ₁ ⇓θ₂) (⊙⇓ ⇓φ₁ ⇓φ₂) ρ₁≡ρ₂ =
    ⟦⟧*⇓-det ⇓θ₂ ⇓φ₂ (⟦⟧*⇓-det ⇓θ₁ ⇓φ₁ ρ₁≡ρ₂)
  ⟦⟧*⇓-det (∷⇓ ⇓u₁ ⇓θ₁) (∷⇓ ⇓u₂ ⇓θ₂) ρ₁≡ρ₂ =
    cong₂ _∷_ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧*⇓-det ⇓θ₁ ⇓θ₂ ρ₁≡ρ₂)
  ⟦⟧*⇓-det ↑⇓ ↑⇓ refl = refl


  ⟨∙⟩⇓-det : ∀ {α β Γ} {u₁ u₂ : Val Γ (α ⇒ β)} {v₁ v₂ : Val Γ α} {w₁ w₂}
    (⇓w₁ : u₁ ⟨∙⟩ v₁ ⇓ w₁) (⇓w₂ : u₂ ⟨∙⟩ v₂ ⇓ w₂)
    (u₁≡u₂ : u₁ ≡ u₂) (v₁≡v₂ : v₁ ≡ v₂) → w₁ ≡ w₂

  ⟨∙⟩⇓-det ne⇓ ne⇓ refl refl = refl
  ⟨∙⟩⇓-det (lam⇓ ⇓w₁) (lam⇓ ⇓w₂) refl refl =
    ⟦⟧⇓-det ⇓w₁ ⇓w₂ refl

--   Quote u₁ ⇓ n₁ →  Quote u₂ ⇓ n₂ → u₁ ≡ u₂ →  n₁ ≡ n₂

mutual

  quote⇓-det : ∀ {α Γ} {u₁ u₂ : Val Γ α} {n₁ n₂}
    (⇓n₁ : Quote u₁ ⇓ n₁) (⇓n₂ : Quote u₂ ⇓ n₂)
    (u₁≡u₂ : u₁ ≡ u₂) →
    n₁ ≡ n₂
  quote⇓-det (⋆⇓ us₁ ⇓ns₁) (⋆⇓ .us₁ ⇓ns₂) refl =
    cong ne (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)
  quote⇓-det (⇒⇓ ⇓u₁ ⇓n₁) (⇒⇓ ⇓u₂ ⇓n₂) refl =
    cong lam (quote⇓-det ⇓n₁ ⇓n₂ (⟨∙⟩⇓-det ⇓u₁ ⇓u₂ refl refl))

  quote*⇓-det : ∀ {α Γ} {us₁ us₂ : NeVal Γ α} {ns₁ ns₂}
    (⇓ns₁ : Quote* us₁ ⇓ ns₁) (⇓ns₂ : Quote* us₂ ⇓ ns₂)
    (us₁≡us₂ : us₁ ≡ us₂) →
    ns₁ ≡ ns₂

  quote*⇓-det var⇓ var⇓ refl = refl
  quote*⇓-det (app⇓ ⇓ns₁ ⇓n₁) (app⇓ ⇓ns₂ ⇓n₂) refl =
    cong₂ app (quote*⇓-det ⇓ns₁ ⇓ns₂ refl) (quote⇓-det ⇓n₁ ⇓n₂ refl)

--   Nf t ⇓ n₁ → Nf t ⇓ n₂ → n₁ ≡ n₂

nf⇓-det : ∀ {α Γ} (t : Tm Γ α)
  {n₁} (⇓n₁ : Nf t ⇓ n₁) {n₂} (⇓n₂ : Nf t ⇓ n₂) →
  n₁ ≡ n₂
nf⇓-det t (nf⇓ ⇓u₁ ⇓n₁) (nf⇓ ⇓u₂ ⇓n₂)
  rewrite ⟦⟧⇓-det ⇓u₁ ⇓u₂ refl
  = quote⇓-det ⇓n₁ ⇓n₂ refl


--
-- Composing OPEs.
--

var≤-≤id : ∀ {α Γ}(x : Var Γ α) → var≤ ≤id x ≡ x
var≤-≤id zero = refl
var≤-≤id (suc x) = cong suc (var≤-≤id x)


-- Variables.

var≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
  (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (x : Var Γ₃ α) →
  var≤ η (var≤ η′ x) ≡ var≤ (η ● η′) x
var≤∘ ≤[] ≤[] x = refl
var≤∘ (≤weak η) η′ x = cong suc (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤weak η′) x = cong suc (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤lift η′) zero = refl
var≤∘ (≤lift η) (≤lift η′) (suc x) = cong suc (var≤∘ η η′ x)

-- Values and environments.

mutual

  val≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (u : Val Γ₃ α) →
    val≤ η (val≤ η′ u) ≡ val≤ (η ● η′) u
  val≤∘ η η′ (ne us) = cong ne (neVal≤∘ η η′ us)
  val≤∘ η η′ (lam t ρ) = cong (lam t) (env≤∘ η η′ ρ)

  neVal≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (us : NeVal Γ₃ α) →
    neVal≤ η (neVal≤ η′ us) ≡ neVal≤ (η ● η′) us
  neVal≤∘ η η′ (var x) =
    cong var (var≤∘ η η′ x)
  neVal≤∘ η η′ (app us u) =
    cong₂ app (neVal≤∘ η η′ us) (val≤∘ η η′ u)

  env≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (ρ : Env Γ₃ α) →
    env≤ η (env≤ η′ ρ) ≡ env≤ (η ● η′) ρ
  env≤∘ η η′ [] = refl
  env≤∘ η η′ (u ∷ ρ) =
    cong₂ _∷_ (val≤∘ η η′ u) (env≤∘ η η′ ρ)

--
-- OPEs commute with evaluation
--

mutual

  ⟦⟧⇓≤ : ∀ {α Β Γ Δ} (η : Β ≤ Γ) {t : Tm Δ α} {ρ : Env Γ Δ} {u : Val Γ α}
    (⇓u : ⟦ t ⟧ ρ ⇓ u) →
    ⟦ t ⟧ env≤ η ρ ⇓ val≤ η u
  ⟦⟧⇓≤ η ø⇓ = ø⇓
  ⟦⟧⇓≤ η (∙⇓ ⇓u ⇓v ⇓w) = ∙⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧⇓≤ η ⇓v) (⟨∙⟩⇓≤ η ⇓w)
  ⟦⟧⇓≤ η ƛ⇓ = ƛ⇓
  ⟦⟧⇓≤ η ([]⇓ ⇓θ ⇓u) = []⇓ (⟦⟧*⇓≤ η ⇓θ) (⟦⟧⇓≤ η ⇓u)

  ⟦⟧*⇓≤ : ∀ {Β Γ Δ Δ′} (η : Β ≤ Γ) {σ : Sub Δ′ Δ} {ρ : Env Γ Δ′} {θ : Env Γ Δ}
    (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) →
    ⟦ σ ⟧* env≤ η ρ ⇓ env≤ η θ
  ⟦⟧*⇓≤ η ι⇓ = ι⇓
  ⟦⟧*⇓≤ η (⊙⇓ ⇓θ₁ ⇓θ₂) = ⊙⇓ (⟦⟧*⇓≤ η ⇓θ₁) (⟦⟧*⇓≤ η ⇓θ₂)
  ⟦⟧*⇓≤ η (∷⇓ ⇓u ⇓θ) = ∷⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧*⇓≤ η ⇓θ)
  ⟦⟧*⇓≤ η ↑⇓ = ↑⇓

  ⟨∙⟩⇓≤ : ∀ {α β Β Γ} (η : Β ≤ Γ)
    {u : Val Γ (α ⇒ β)} {v : Val Γ α} {w : Val Γ β}
    (⇓w : u ⟨∙⟩ v ⇓ w) →
    val≤ η u ⟨∙⟩ val≤ η v ⇓ val≤ η w
  ⟨∙⟩⇓≤ η ne⇓ = ne⇓
  ⟨∙⟩⇓≤ η (lam⇓ ⇓v) = lam⇓ (⟦⟧⇓≤ η ⇓v)

--
-- OPEs commute with val≤ wk.
--

wk∘val≤ : ∀ {Β Γ α β} (η : Β ≤ Γ) (u : Val Γ α) →
  val≤ wk (val≤ η u) ≡ val≤ (≤lift {β} η) (val≤ wk u)
wk∘val≤ η u = begin
  val≤ wk (val≤ η u)
    ≡⟨⟩
  val≤ wk (val≤ η u)
    ≡⟨ val≤∘ wk η u ⟩
  val≤ (≤weak (≤id ● η)) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (≤id●η η) ⟩
  val≤ (≤weak η) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (sym $ η●≤id η) ⟩
  val≤ (≤weak (η ● ≤id)) u
    ≡⟨⟩
  val≤ (≤lift η ● wk) u
    ≡⟨ sym $ val≤∘ (≤lift η) wk u ⟩
  val≤ (≤lift η) (val≤ wk u)
    ≡⟨⟩
  val≤ (≤lift η) (val≤ wk u)
  ∎
  where open ≡-Reasoning

--
-- OPEs commute with embeddings.
--

embVar∘≤ :  ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  embVar (var≤ η x) ≈ embVar x [ sub≤ η ]
embVar∘≤ ≤[] x = ≈sym ≈id
embVar∘≤ (≤weak η) zero = begin
  embVar (var≤ (≤weak η) zero)
    ≡⟨⟩
  embVar (var≤ η zero) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η zero) ≈≈refl ⟩
  ø [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  ø [ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar zero [ sub≤ (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤weak η) (suc x) = begin
  embVar (var≤ (≤weak η) (suc x))
    ≡⟨⟩
  embVar (var≤ η (suc x)) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η (suc x)) ≈≈refl ⟩
  embVar x [ ↑ ] [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  embVar x [ ↑ ] [ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar (suc x) [ sub≤ (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) zero = begin
  embVar (var≤ (≤lift η) zero)
    ≡⟨⟩
  ø
    ≈⟨ ≈sym ≈proj ⟩
  ø [ ø ∷ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar zero [ sub≤ (≤lift η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) (suc x) = begin
  embVar (var≤ (≤lift η) (suc x))
    ≡⟨⟩
  embVar (var≤ η x) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η x) ≈≈refl ⟩
  embVar x [ sub≤ η ] [ ↑ ]
    ≈⟨ ≈sym ≈comp ⟩
  embVar x [ sub≤ η ⊙ ↑ ]
    ≈⟨ ≈cong[] ≈refl (≈≈sym ≈≈wk) ⟩
  embVar x [ ↑ ⊙ (ø ∷ sub≤ η ⊙ ↑) ]
    ≈⟨ ≈comp ⟩
  embVar x [ ↑ ] [ ø ∷ sub≤ η ⊙ ↑ ]
    ≡⟨⟩
  embVar (suc x) [ sub≤ (≤lift η) ]
  ∎
  where open ≈-Reasoning

mutual

  embVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (u : Val Γ α) →
    embVal (val≤ η u) ≈ embVal u [ sub≤ η ]
  embVal∘≤ η (ne us) = embNeVal∘≤ η us
  embVal∘≤ η (lam t ρ) = begin
    embVal (val≤ η (lam t ρ))
      ≡⟨⟩
    (ƛ t) [ embEnv (env≤ η ρ) ]
      ≈⟨ ≈cong[] ≈refl (embEnv∘≤ η ρ) ⟩
    (ƛ t) [ embEnv ρ ⊙ sub≤ η ]
      ≈⟨ ≈comp  ⟩
    (ƛ t) [ embEnv ρ ] [ sub≤ η ]
      ≡⟨⟩
    embVal (lam t ρ) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embNeVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : NeVal Γ α) →
    embNeVal (neVal≤ η us) ≈ embNeVal us [ sub≤ η ]
  embNeVal∘≤ η (var x) = embVar∘≤ η x
  embNeVal∘≤ η (app us u) = begin
    embNeVal (neVal≤ η (app us u))
      ≡⟨⟩
    embNeVal (neVal≤ η us) ∙ embVal (val≤ η u)
      ≈⟨ ≈cong∙ (embNeVal∘≤ η us) (embVal∘≤ η u) ⟩
    embNeVal us [ sub≤ η ] ∙ embVal u [ sub≤ η ]
      ≈⟨ ≈sym ≈app ⟩
    (embNeVal us ∙ embVal u) [ sub≤ η ]
      ≡⟨⟩
    embNeVal (app us u) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embEnv∘≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (ρ : Env Γ Δ) →
    embEnv (env≤ η ρ) ≈≈ embEnv ρ ⊙ sub≤ η
  embEnv∘≤ ≤[] [] = ≈≈sym ≈≈idr
  embEnv∘≤ {Γ = []} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≈≈cong⊙ (embEnv∘≤ η []) ≈≈refl ⟩
    (ı ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≈≈assoc ⟩
    ı ⊙ sub≤ η ⊙ ↑
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤weak η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ {Γ = α ∷ Γ} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≈≈cong⊙ (embEnv∘≤ η []) ≈≈refl ⟩
    ((sub-from-[] ⊙ ↑) ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≈≈assoc ⟩
    (sub-from-[] ⊙ ↑) ⊙ (sub≤ η ⊙ ↑)
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤weak η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ (≤lift η) [] = begin
    embEnv (env≤ (≤lift η) [])
      ≡⟨⟩
    sub-from-[] ⊙ ↑
      ≈⟨ ≈≈cong⊙ (embEnv∘≤ η []) ≈≈refl ⟩
    (sub-from-[] ⊙ sub≤ η) ⊙ ↑
      ≈⟨ ≈≈assoc ⟩
    sub-from-[] ⊙ (sub≤ η ⊙ ↑)
      ≈⟨ ≈≈cong⊙ ≈≈refl (≈≈sym ≈≈wk) ⟩
    sub-from-[] ⊙ (↑ ⊙ (ø ∷ sub≤ η ⊙ ↑))
      ≈⟨ ≈≈sym ≈≈assoc ⟩
    (sub-from-[] ⊙ ↑) ⊙ (ø ∷ sub≤ η ⊙ ↑)
      ≡⟨⟩
    embEnv [] ⊙ sub≤ (≤lift η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ η (u ∷ ρ) = begin
    embEnv (env≤ η (u ∷ ρ))
      ≡⟨⟩
    embVal (val≤ η u) ∷ embEnv (env≤ η ρ)
      ≈⟨ ≈≈cong∷ (embVal∘≤ η u) (embEnv∘≤ η ρ) ⟩
    embVal u [ sub≤ η ] ∷ embEnv ρ ⊙ sub≤ η
      ≈⟨ ≈≈sym ≈≈cons ⟩
    (embVal u ∷ embEnv ρ) ⊙ sub≤ η
      ≡⟨⟩
    embEnv (u ∷ ρ) ⊙ sub≤ η
    ∎
    where open ≈≈-Reasoning

-- Normal forms.

mutual

  embNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (n : Nf Γ α) →
    embNf (nf≤ η n) ≈ embNf n [ sub≤ η ]
  embNf∘≤ η (ne ns) = embNeNf∘≤ η ns
  embNf∘≤ η (lam n) = begin
    embNf (nf≤ η (lam n))
      ≡⟨⟩
    ƛ embNf (nf≤ (≤lift η) n)
      ≈⟨ ≈congƛ (embNf∘≤ (≤lift η) n) ⟩
    ƛ embNf n [ ø ∷ sub≤ η ⊙ ↑ ]
      ≈⟨ ≈sym ≈lam ⟩
    (ƛ embNf n) [ sub≤ η ]
      ≡⟨⟩
    embNf (lam n) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

  embNeNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (ns : NeNf Γ α) →
    embNeNf (neNf≤ η ns) ≈ embNeNf ns [ sub≤ η ]
  embNeNf∘≤ η (var x) = embVar∘≤ η x
  embNeNf∘≤ η (app ns u) = begin
    embNeNf (neNf≤ η (app ns u))
      ≡⟨⟩
    embNeNf (neNf≤ η ns) ∙ embNf (nf≤ η u)
      ≈⟨ ≈cong∙ (embNeNf∘≤ η ns) (embNf∘≤ η u) ⟩
    (embNeNf ns [ sub≤ η ]) ∙ (embNf u [ sub≤ η ])
      ≈⟨ ≈sym ≈app ⟩
    (embNeNf ns ∙ embNf u) [ sub≤ η ]
      ≡⟨⟩
    embNeNf (app ns u) [ sub≤ η ]
    ∎
    where open ≈-Reasoning

mutual

  quote≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {u : Val Γ α} {n : Nf Γ α}
    (⇓n : Quote u ⇓ n) →
      Quote val≤ η u ⇓ nf≤ η n

  quote≤ η (⋆⇓ us ⇓ns) =
    ⋆⇓ (neVal≤ η us) (quote*≤ η ⇓ns)
  quote≤ η (⇒⇓ {f = f} {u} {n} ⇓u ⇓n) =
    ⇒⇓ ⇓u′′′ ⇓n′
    where
      ⇓u′ : val≤ (≤lift η) (val≤ wk f) ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u
      ⇓u′ = ⟨∙⟩⇓≤ (≤lift η) ⇓u
      ⇓u′′′ : val≤ wk (val≤ η f) ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u
      ⇓u′′′ = subst (λ w → w ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u)
                    (sym $ wk∘val≤ η f) ⇓u′
      ⇓n′ : Quote val≤ (≤lift η) u ⇓ nf≤ (≤lift η) n
      ⇓n′ = quote≤ (≤lift η) ⇓n

  quote*≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {us : NeVal Γ α} {ns : NeNf Γ α}
    (⇓ns : Quote* us ⇓ ns) →
      Quote* neVal≤ η us ⇓ neNf≤ η ns

  quote*≤ η var⇓ = var⇓
  quote*≤ η (app⇓ ⇓ns ⇓n) =
    app⇓ (quote*≤ η ⇓ns) (quote≤ η ⇓n)



embNe≈≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : NeVal Γ α) (ns : NeNf Γ α) →
  (p : embNeVal us ≈ embNeNf ns) →
     embNeVal (neVal≤ η us) ≈ embNeNf (neNf≤ η ns)
embNe≈≤ η us ns p = begin
  embNeVal (neVal≤ η us)
    ≈⟨ embNeVal∘≤ η us ⟩
  embNeVal us [ sub≤ η ]
    ≈⟨ ≈cong[] p ≈≈refl ⟩
  embNeNf ns [ sub≤ η ]
    ≈⟨ ≈sym (embNeNf∘≤ η ns) ⟩
  embNeNf (neNf≤ η ns)
  ∎
  where open ≈-Reasoning
