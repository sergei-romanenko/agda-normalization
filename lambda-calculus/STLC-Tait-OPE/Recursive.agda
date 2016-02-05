module STLC-Tait-OPE.Recursive where

open import STLC-Tait-OPE.Util
open import STLC-Tait-OPE.Syntax

--
-- Recursive normalizer.
--

{-# TERMINATING #-}
mutual

  infixl 5 _⟨∙⟩_

  ⟦_⟧_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) → Val Γ α
  ⟦ ø ⟧ (u ∷ ρ) = u
  ⟦ t ∙ t′ ⟧ ρ = ⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ
  ⟦ ƛ t ⟧ ρ = lam t ρ
  ⟦ t [ σ ] ⟧ ρ = ⟦ t ⟧ (⟦ σ ⟧* ρ)

  ⟦_⟧*_ : ∀ {Β Γ Δ} (σ : Sub Β Γ) (ρ : Env Δ Β) → Env Δ Γ
  ⟦ ı ⟧* ρ = ρ
  ⟦ σ ⊙ σ′ ⟧* ρ = ⟦ σ ⟧* (⟦ σ′ ⟧* ρ)
  ⟦ t ∷ σ ⟧* ρ = ⟦ t ⟧ ρ ∷ ⟦ σ ⟧* ρ
  ⟦ ↑ ⟧* (u ∷ ρ) = ρ

  _⟨∙⟩_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) → Val Γ β
  ne us ⟨∙⟩ u = ne (app us u)
  lam t ρ ⟨∙⟩ u = ⟦ t ⟧ (u ∷ ρ)

⟦III⟧ : ⟦ III ⟧ ([] {[]}) ≡ lam ø []
⟦III⟧ = refl

⟦SKK⟧ : ⟦ SKK {⋆} ⟧ ([] {[]}) ≡
  lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
      (lam (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))
⟦SKK⟧ = refl

⟦SKK∙I⟧ : ⟦ SKK ∙ I {⋆} ⟧ ([] {[]}) ≡ lam ø []
⟦SKK∙I⟧ = refl


{-# TERMINATING #-}
mutual

  ⌜_⌝ : ∀ {α Γ} (u : Val Γ α) → Nf Γ α
  ⌜_⌝ {⋆} (ne us) = ne ⌜ us ⌝*
  ⌜_⌝ {α ⇒ β} f =
    lam ⌜ val≤ wk f ⟨∙⟩ ne (var zero) ⌝

  ⌜_⌝* : ∀ {α Γ} (us : NeVal Γ α) → NeNf Γ α
  ⌜ var x ⌝* = var x
  ⌜ app us u ⌝* = app ⌜ us ⌝* ⌜ u ⌝

-- Normalizer.

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf t = ⌜ ⟦ t ⟧ id-env ⌝

nf-III : nf III ≡ lam (ne (var zero))
nf-III = refl

nf-SKK : nf (SKK {⋆}) ≡ lam (ne (var zero))
nf-SKK = refl

nf-SKK∙I : nf (SKK ∙ I {⋆}) ≡ lam (ne (var zero))
nf-SKK∙I = refl


--
-- Stability: nf (embNf n) ≡ n .
--

var≤∘suc : ∀ {α γ Β Γ} (η : Β ≤ γ ∷ Γ) (x : Var Γ α) →
  var≤ η (suc x) ≡ var≤ (η ● wk) x
var≤∘suc (≤weak η) x =
  cong suc (var≤∘suc η x)
var≤∘suc (≤lift η) x
  rewrite η ● ≤id ≡ η ∋ η●≤id η
  = refl

⟦⟧∘embVar≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  ⟦ embVar x ⟧ (env≤ η id-env) ≡ ne (var (var≤ η x))
⟦⟧∘embVar≤ η zero = refl
⟦⟧∘embVar≤ η (suc x)
  rewrite env≤∘ η wk id-env | var≤∘suc η x
  = ⟦⟧∘embVar≤ (η ● wk) x

⟦⟧∘embVar : ∀ {α Γ} (x : Var Γ α) →
  ⟦ embVar x ⟧ id-env ≡ ne (var x)
⟦⟧∘embVar x = begin
  ⟦ embVar x ⟧ id-env
    ≡⟨ cong (⟦_⟧_ (embVar x)) (sym $ env≤∘≤id id-env) ⟩
  ⟦ embVar x ⟧ (env≤ ≤id id-env)
    ≡⟨ ⟦⟧∘embVar≤ ≤id x ⟩
  ne (var (var≤ ≤id x))
    ≡⟨ cong (ne ∘′ var) (var≤∘≤id x) ⟩
  ne (var x)
  ∎
  where open ≡-Reasoning

mutual

  stable : ∀ {α Γ} (n : Nf Γ α) → nf (embNf n) ≡ n
  stable (ne ns)
    with stable* ns
  ... | us , ≡ne-us , ≡ns = begin
    ⌜ ⟦ embNeNf ns ⟧ id-env ⌝
      ≡⟨ cong ⌜_⌝ ≡ne-us ⟩
    ⌜ ne us ⌝
      ≡⟨⟩
    ne ⌜ us ⌝*
      ≡⟨ cong ne ≡ns ⟩
    ne ns
    ∎
    where open ≡-Reasoning
  stable (lam n) =
    cong lam (stable n)

  stable* : ∀ {α Γ} (ns : NeNf Γ α) →
    ∃ λ (us : NeVal Γ α) →
      ⟦ embNeNf ns ⟧ id-env ≡ ne us × ⌜ us ⌝* ≡ ns
  stable* (var x) =
    var x , ⟦⟧∘embVar x , refl
  stable* (app ns n)
    with stable* ns | stable n
  ... | us , ≡ne-us , ≡ns | ≡n
    with ⟦ embNeNf ns ⟧ id-env | ⟦ embNf n ⟧ id-env
  ... | ne-us′ | u 
    rewrite ≡ne-us
    = app us u , refl , cong₂ app ≡ns ≡n

--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
-- (Normalisation takes convertible terms to identical normal forms.)
--

{-# TERMINATING #-}
mutual

  ⟦⟧∘≤ : ∀ {α Β Γ Δ} (η : Β ≤ Γ) (t : Tm Δ α) (ρ : Env Γ Δ) → 
    ⟦ t ⟧ (env≤ η ρ) ≡ val≤ η (⟦ t ⟧ ρ)
  ⟦⟧∘≤ η ø (u ∷ ρ) = refl
  ⟦⟧∘≤ η (t ∙ t′) ρ = begin
    ⟦ t ⟧ env≤ η ρ ⟨∙⟩ ⟦ t′ ⟧ env≤ η ρ
      ≡⟨ cong₂ _⟨∙⟩_ (⟦⟧∘≤ η t ρ) (⟦⟧∘≤ η t′ ρ) ⟩
    val≤ η (⟦ t ⟧ ρ) ⟨∙⟩ val≤ η (⟦ t′ ⟧ ρ)
      ≡⟨ ⟨∙⟩∘≤ η (⟦ t ⟧ ρ) (⟦ t′ ⟧ ρ) ⟩
    val≤ η (⟦ t ⟧ ρ ⟨∙⟩ ⟦ t′ ⟧ ρ)
    ∎
    where open ≡-Reasoning
  ⟦⟧∘≤ η (ƛ t) ρ =
    cong (lam t) refl
  ⟦⟧∘≤ η (t [ σ ]) ρ = begin
    ⟦ t ⟧ (⟦ σ ⟧* env≤ η ρ)
      ≡⟨ cong (⟦_⟧_ t) (⟦⟧*∘≤ η σ ρ) ⟩
    ⟦ t ⟧ env≤ η (⟦ σ ⟧* ρ)
      ≡⟨ ⟦⟧∘≤ η t (⟦ σ ⟧* ρ) ⟩
    val≤ η (⟦ t ⟧ (⟦ σ ⟧* ρ))
    ∎
    where open ≡-Reasoning

  ⟦⟧*∘≤ : ∀ {Β Γ Δ Δ′} (η : Β ≤ Γ) (σ : Sub Δ Δ′) (ρ : Env Γ Δ) →
    ⟦ σ ⟧* (env≤ η ρ) ≡ env≤ η (⟦ σ ⟧* ρ)
  ⟦⟧*∘≤ η ı ρ = refl
  ⟦⟧*∘≤ η (σ ⊙ σ′) ρ = begin
    ⟦ σ ⟧* (⟦ σ′ ⟧* env≤ η ρ)
      ≡⟨ cong (⟦_⟧*_ σ) (⟦⟧*∘≤ η σ′ ρ) ⟩
    ⟦ σ ⟧* env≤ η (⟦ σ′ ⟧* ρ)
      ≡⟨ ⟦⟧*∘≤ η σ (⟦ σ′ ⟧* ρ) ⟩
    env≤ η (⟦ σ ⟧* (⟦ σ′ ⟧* ρ))
    ∎
    where open ≡-Reasoning
  ⟦⟧*∘≤ η (t ∷ σ) ρ =
    cong₂ _∷_ (⟦⟧∘≤ η t ρ) (⟦⟧*∘≤ η σ ρ)
  ⟦⟧*∘≤ η ↑ (u ∷ ρ) = refl


  ⟨∙⟩∘≤ : ∀ {α β Γ Δ} (η : Γ ≤ Δ) (u : Val Δ (α ⇒ β)) (v : Val Δ α) →
    val≤ η u ⟨∙⟩ val≤ η v ≡ val≤ η (u ⟨∙⟩ v)
  ⟨∙⟩∘≤ η (ne us) v = refl
  ⟨∙⟩∘≤ η (lam t ρ) v =
    ⟦⟧∘≤ η t (v ∷ ρ)


{-# TERMINATING #-}
mutual

  quote∘≤ : ∀ {α Γ Δ} (η : Γ ≤ Δ) (u : Val Δ α) → 
    ⌜ val≤ η u ⌝ ≡ nf≤ η ⌜ u ⌝

  quote∘≤ {⋆} η (ne us) =
    cong ne (quote*∘≤ η us)
  quote∘≤ {α ⇒ β} η u = cong lam r
    where
    open ≡-Reasoning
    p = begin
      ≤id ● η
        ≡⟨ ≤id●η η ⟩
      η
        ≡⟨ sym $ η●≤id η ⟩
      η ● ≤id ∎
    q = begin
      val≤ wk (val≤ η u) ⟨∙⟩ ne (var zero)
        ≡⟨ cong₂ _⟨∙⟩_ (val≤∘ wk η u) refl ⟩
      val≤ (wk ● η) u ⟨∙⟩ ne (var zero)
        ≡⟨⟩
      val≤ (≤weak (≤id ● η)) u ⟨∙⟩ ne (var zero)
        ≡⟨ cong (λ η′ → val≤ (≤weak η′) u ⟨∙⟩ ne (var zero)) p ⟩
      val≤ (≤weak (η ● ≤id)) u ⟨∙⟩ ne (var zero)
        ≡⟨ cong₂ _⟨∙⟩_ (sym $ val≤∘ (≤lift η) wk u) refl ⟩
      val≤ (≤lift η) (val≤ wk u) ⟨∙⟩ ne (var zero)
        ≡⟨⟩
      val≤ (≤lift η) (val≤ wk u) ⟨∙⟩ val≤ (≤lift η) (ne (var zero))
        ≡⟨ ⟨∙⟩∘≤ (≤lift η) (val≤ wk u) (ne (var zero)) ⟩
      val≤ (≤lift η) (val≤ wk u ⟨∙⟩ ne (var zero))
      ∎
    r = begin
      ⌜ val≤ wk (val≤ η u) ⟨∙⟩ ne (var zero) ⌝
        ≡⟨ cong ⌜_⌝ q ⟩
      ⌜ val≤ (≤lift η) (val≤ wk u ⟨∙⟩ ne (var zero)) ⌝
        ≡⟨ quote∘≤ (≤lift η) (val≤ wk u ⟨∙⟩ ne (var zero)) ⟩
      nf≤ (≤lift η) ⌜ val≤ wk u ⟨∙⟩ ne (var zero) ⌝
      ∎

  quote*∘≤ : ∀ {α Γ Δ} (η : Γ ≤ Δ) (us : NeVal Δ α) →
    ⌜ neVal≤ η us ⌝* ≡ neNf≤ η ⌜ us ⌝*

  quote*∘≤ η (var x) = refl
  quote*∘≤ η (app us u) =
    cong₂ app (quote*∘≤ η us) (quote∘≤ η u)


infix 4 _~_ _~~_

_~_ : ∀ {α Γ} (u₁ u₂ : Val Γ α) → Set
_~_ {⋆} (ne us₁) (ne us₂) = ⌜ us₁ ⌝* ≡ ⌜ us₂ ⌝*
_~_ {α ⇒ β} {Γ} f₁ f₂ = ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} →
  u₁ ~ u₂ → val≤ η f₁ ⟨∙⟩ u₁ ~ val≤ η f₂ ⟨∙⟩ u₂

data _~~_ : ∀ {Γ Δ} (ρ₁ ρ₂ : Env Γ Δ) → Set where
  [] :  ∀ {Γ} →
    _~~_ {Γ} [] []
  _∷_ : ∀ {α Γ Δ} {u₁ u₂ : Val Γ α} {ρ₁ ρ₂ : Env Γ Δ} →
    u₁ ~ u₂ → ρ₁ ~~ ρ₂ →
    u₁ ∷ ρ₁ ~~ u₂ ∷ ρ₂

module DifferentValuesMayBeEquivalent where

  -- The subtle point is that two different values may have
  -- identical  normal forms.

  val-III : Val [] (⋆ ⇒ ⋆)
  val-III = lam ø []

  val-SKK : Val [] (⋆ ⇒ ⋆)
  val-SKK =
    lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
      (lam {⋆} {⋆ ⇒ ⋆} (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))

  val-III~val-III : val-III ~ val-III
  val-III~val-III η u₁~u₂ = u₁~u₂

mutual

  ~sym : ∀ {α Γ} {u₁ u₂ : Val Γ α} → u₁ ~ u₂ → u₂ ~ u₁
  ~sym {⋆} {Γ} {ne us} {ne us′} u~u′ = sym u~u′
  ~sym {α ⇒ β} p η u₁~u₂ =
    ~sym (p η (~sym u₁~u₂))

  ~~sym :  ∀ {Γ Δ} {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₁
  ~~sym [] = []
  ~~sym (u₁~u₂ ∷ ρ₁~~ρ₂) = ~sym u₁~u₂ ∷ ~~sym ρ₁~~ρ₂


mutual

  ~trans : ∀ {α Γ} {u₁ u₂ u₃ : Val Γ α} →
    u₁ ~ u₂ → u₂ ~ u₃ → u₁ ~ u₃
  ~trans {⋆} {Γ} {ne us₁} {ne us₂} {ne us₃} u₁~u₂ u₂~u₃ = begin
    ⌜ us₁ ⌝*
      ≡⟨ u₁~u₂ ⟩
    ⌜ us₂ ⌝*
      ≡⟨ u₂~u₃ ⟩
    ⌜ us₃ ⌝*
    ∎
    where open ≡-Reasoning
  ~trans {α ⇒ β} p q η v₁~v₂ =
    ~trans (p η (~refl′ v₁~v₂)) (q η v₁~v₂)

  ~~trans : ∀ {Γ Δ} {ρ₁ ρ₂ ρ₃ : Env Γ Δ} →
    ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₃ → ρ₁ ~~ ρ₃
  ~~trans [] [] = []
  ~~trans (u₁~u₂ ∷ ρ₁~~ρ₂) (u₂~u₃ ∷ ρ₂~~ρ₃) =
    ~trans u₁~u₂ u₂~u₃ ∷ ~~trans ρ₁~~ρ₂ ρ₂~~ρ₃

  ~refl′ : ∀ {α Γ} {u u′ : Val Γ α} → u ~ u′ → u ~ u
  ~refl′ u~u′ = ~trans u~u′ (~sym u~u′)

  ~~refl′ : ∀ {Γ Δ} {ρ ρ′ : Env Γ Δ} → ρ ~~ ρ′ → ρ ~~ ρ
  ~~refl′ ρ~~ρ′ = ~~trans ρ~~ρ′ (~~sym ρ~~ρ′)

~≤ : ∀ {α Γ Δ} (η : Γ ≤ Δ) {u₁ u₂ : Val Δ α} → u₁ ~ u₂ →
       val≤ η u₁ ~ val≤ η u₂
~≤ {⋆} η {ne us₁} {ne us₂} u₁~u₂ = begin
  ⌜ neVal≤ η us₁ ⌝*
    ≡⟨ quote*∘≤ η us₁ ⟩
  neNf≤ η ⌜ us₁ ⌝*
    ≡⟨ cong (neNf≤ η) u₁~u₂ ⟩
  neNf≤ η ⌜ us₂ ⌝*
    ≡⟨ sym $ quote*∘≤ η us₂ ⟩
  ⌜ neVal≤ η us₂ ⌝*
  ∎
  where open ≡-Reasoning
~≤ {α ⇒ β} η {u₁} {u₂} p {B} η′ {v₁} {v₂} v₁~v₂
  rewrite val≤ η′ (val≤ η u₁) ≡ val≤ (η′ ● η) u₁ ∋ val≤∘ η′ η u₁ |
          val≤ η′ (val≤ η u₂) ≡ val≤ (η′ ● η) u₂ ∋ val≤∘ η′ η u₂
  = p (η′ ● η) v₁~v₂

~~≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → 
        env≤ η ρ₁ ~~ env≤ η ρ₂
~~≤ η [] = []
~~≤ η (u₁~u₂ ∷ ρ₁~~ρ₂) = ~≤ η u₁~u₂ ∷ ~~≤ η ρ₁~~ρ₂


mutual

  ~cong⟦≡⟧ : ∀ {α Γ Δ} (t : Tm Δ α) {ρ₁ ρ₂ : Env Γ Δ} →
    ρ₁ ~~ ρ₂ →
    ⟦ t ⟧ ρ₁ ~ ⟦ t ⟧ ρ₂

  ~cong⟦≡⟧ ø (u₁~u₂ ∷ ρ₁~~ρ₂) = u₁~u₂
  ~cong⟦≡⟧ (t ∙ t′) {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~cong⟦≡⟧ t′ ρ₁~~ρ₂
  ... | u₁~u₂ | v₁~v₂
    with u₁~u₂ ≤id v₁~v₂
  ... | uv₁~uv₂
    rewrite val≤ ≤id (⟦ t ⟧ ρ₁) ≡ ⟦ t ⟧ ρ₁ ∋ val≤∘≤id _ |
            val≤ ≤id (⟦ t ⟧ ρ₂) ≡ ⟦ t ⟧ ρ₂ ∋ val≤∘≤id _
    = uv₁~uv₂
  ~cong⟦≡⟧ (ƛ t) ρ₁~~ρ₂ η v₁~v₂ =
    ~cong⟦≡⟧ t (v₁~v₂ ∷ ~~≤ η ρ₁~~ρ₂)
  ~cong⟦≡⟧ (t [ σ ]) ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t (~~cong⟦≡⟧* σ ρ₁~~ρ₂)

  ~~cong⟦≡⟧* : ∀ {Γ Δ Δ′} (σ : Sub Δ Δ′) {ρ₁ ρ₂ : Env Γ Δ} →
    ρ₁ ~~ ρ₂ →
    ⟦ σ ⟧* ρ₁ ~~ ⟦ σ ⟧* ρ₂

  ~~cong⟦≡⟧* ı ρ₁~~ρ₂ = ρ₁~~ρ₂
  ~~cong⟦≡⟧* (σ ⊙ σ′) ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ (~~cong⟦≡⟧* σ′ ρ₁~~ρ₂)
  ~~cong⟦≡⟧* (t ∷ σ) ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t ρ₁~~ρ₂ ∷ ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦≡⟧* ↑ (u₁~u₂ ∷ ρ₁~~ρ₂) = ρ₁~~ρ₂


mutual

  ~cong⟦⟧ : ∀ {α Γ Δ}
    {t₁ t₂ : Tm Δ α} (t₁≈t₂ : t₁ ≈ t₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ⟦ t₁ ⟧ ρ₁ ~ ⟦ t₂ ⟧ ρ₂

  ~cong⟦⟧ {t₁ = t} ≈refl ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t ρ₁~~ρ₂
  ~cong⟦⟧ (≈sym t₁≈t₂) ρ₁~~ρ₂ =
    ~sym (~cong⟦⟧ t₁≈t₂ (~~sym ρ₁~~ρ₂))
  ~cong⟦⟧ (≈trans t₁≈t₂ t₂≈t₃) ρ₁~~ρ₂ =
    ~trans (~cong⟦⟧ t₁≈t₂ (~~refl′ ρ₁~~ρ₂)) (~cong⟦⟧ t₂≈t₃ ρ₁~~ρ₂)
  ~cong⟦⟧ {t₁ = f₁ ∙ t₁} {t₂ = f₂ ∙ t₂} (≈cong∙ f₁≈f₂ t₁≈t₂) {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂
  ... | v₁~v₂
    with ~cong⟦⟧ f₁≈f₂ ρ₁~~ρ₂ ≤id v₁~v₂
  ... | w₁~w₂
    rewrite val≤ ≤id (⟦ f₁ ⟧ ρ₁) ≡ ⟦ f₁ ⟧ ρ₁ ∋ val≤∘≤id _ |
            val≤ ≤id (⟦ f₂ ⟧ ρ₂) ≡ ⟦ f₂ ⟧ ρ₂ ∋ val≤∘≤id _
    = w₁~w₂
  ~cong⟦⟧ (≈cong[] t₁≈t₂ σ₁≈≈σ₂) ρ₁~~ρ₂ =
    ~cong⟦⟧ t₁≈t₂ (~~cong⟦⟧* σ₁≈≈σ₂ ρ₁~~ρ₂)
  ~cong⟦⟧ (≈congƛ t₁≈t₂) ρ₁~~ρ₂ η v₁~v₂ =
    ~cong⟦⟧ t₁≈t₂ (v₁~v₂ ∷ ~~≤ η ρ₁~~ρ₂)
  ~cong⟦⟧ {t₁ = ø [ t ∷ σ ]} ≈proj ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t ρ₁~~ρ₂
  ~cong⟦⟧ {t₁ = t [ ı ]} ≈id ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t ρ₁~~ρ₂
  ~cong⟦⟧ {t₁ = t [ σ ⊙ σ′ ]} ≈comp ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t (~~cong⟦≡⟧* σ (~~cong⟦≡⟧* σ′ ρ₁~~ρ₂))
  ~cong⟦⟧ {t₁ = (ƛ t) [ σ ]} ≈lam {ρ₁} {ρ₂} ρ₁~~ρ₂ {B} η {v₁} {v₂} v₁~v₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁~θ₂
    with ~cong⟦≡⟧ t (v₁~v₂ ∷ ~~≤ η θ₁~θ₂)
  ... | w₁~w₂
    rewrite ⟦ σ ⟧* env≤ η ρ₂ ≡ env≤ η (⟦ σ ⟧* ρ₂) ∋ ⟦⟧*∘≤ η σ ρ₂
    = w₁~w₂
  ~cong⟦⟧ {t₁ = (t ∙ t′) [ σ ]} ≈app {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁~~θ₂
    with ~cong⟦≡⟧ t′ θ₁~~θ₂
  ... | v₁~v₂
    with ~cong⟦≡⟧ t θ₁~~θ₂ ≤id v₁~v₂
  ... | w₁~w₂
    rewrite val≤ ≤id (⟦ t ⟧ (⟦ σ ⟧* ρ₁)) ≡ ⟦ t ⟧ (⟦ σ ⟧* ρ₁) ∋ val≤∘≤id _ |
            val≤ ≤id (⟦ t ⟧ (⟦ σ ⟧* ρ₂)) ≡ ⟦ t ⟧ (⟦ σ ⟧* ρ₂) ∋ val≤∘≤id _
    = w₁~w₂
  ~cong⟦⟧ {t₁ = (ƛ t) [ σ ] ∙ t′} ≈βσ {ρ₁} {ρ₂} ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t (~cong⟦≡⟧ t′ ρ₁~~ρ₂ ∷ ~~cong⟦≡⟧* σ ρ₁~~ρ₂)
  ~cong⟦⟧ {t₁ = t} ≈η {ρ₁} {ρ₂} ρ₁~~ρ₂ {Β} η {v₁} {v₂} v₁~v₂
    with ~cong⟦≡⟧ t (~~≤ η ρ₁~~ρ₂) ≤id v₁~v₂
  ... | w₁~w₂
    rewrite val≤ ≤id (⟦ t ⟧ env≤ η ρ₁) ≡ ⟦ t ⟧ env≤ η ρ₁ ∋ val≤∘≤id _ |
            val≤ ≤id (⟦ t ⟧ env≤ η ρ₂) ≡ ⟦ t ⟧ env≤ η ρ₂ ∋ val≤∘≤id _ |
            ⟦ t ⟧ env≤ η ρ₁ ≡ val≤ η (⟦ t ⟧ ρ₁) ∋ ⟦⟧∘≤ η t ρ₁
    = w₁~w₂

  ~~cong⟦⟧* : ∀ {Γ Δ Δ′}
    {σ₁ σ₂ : Sub Δ Δ′} (σ₁≈≈σ₂ : σ₁ ≈≈ σ₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ⟦ σ₁ ⟧* ρ₁ ~~ ⟦ σ₂ ⟧* ρ₂

  ~~cong⟦⟧* {σ₁ = σ} ≈≈refl ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦⟧* (≈≈sym σ₁≈≈σ₂) ρ₁~~ρ₂ =
    ~~sym (~~cong⟦⟧* σ₁≈≈σ₂ (~~sym ρ₁~~ρ₂))
  ~~cong⟦⟧* (≈≈trans σ₁≈≈σ₂ σ₂≈≈σ₃) ρ₁~~ρ₂ =
    ~~trans (~~cong⟦⟧* σ₁≈≈σ₂ (~~refl′ ρ₁~~ρ₂)) (~~cong⟦⟧* σ₂≈≈σ₃ ρ₁~~ρ₂)
  ~~cong⟦⟧* (≈≈cong⊙ σ₁≈≈σ₂ τ₁≈≈τ₂) ρ₁~~ρ₂ =
    ~~cong⟦⟧* σ₁≈≈σ₂ (~~cong⟦⟧* τ₁≈≈τ₂ ρ₁~~ρ₂)
  ~~cong⟦⟧* (≈≈cong∷ t₁≈t₂ σ₁≈≈σ₂) ρ₁~~ρ₂ =
    ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂ ∷ ~~cong⟦⟧* σ₁≈≈σ₂ ρ₁~~ρ₂
  ~~cong⟦⟧* {σ₁ = (σ₁ ⊙ σ₂) ⊙ σ₃} ≈≈assoc ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ₁ (~~cong⟦≡⟧* σ₂ (~~cong⟦≡⟧* σ₃ ρ₁~~ρ₂))
  ~~cong⟦⟧* {σ₂ = σ} ≈≈idl ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦⟧* {σ₂ = σ} ≈≈idr ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦⟧* {σ₁ = ↑ ⊙ (t ∷ σ)} ≈≈wk ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦⟧* {σ₁ = (t ∷ σ) ⊙ σ′} ≈≈cons ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t (~~cong⟦≡⟧* σ′ ρ₁~~ρ₂) ∷ ~~cong⟦≡⟧* σ (~~cong⟦≡⟧* σ′ ρ₁~~ρ₂)
  ~~cong⟦⟧* ≈≈id∷ (u₁~u₂ ∷ ρ₁~~ρ₂) =
    u₁~u₂ ∷ ρ₁~~ρ₂

mutual

  ~confl : ∀ {α Γ} {u₁ u₂ : Val Γ α} → 
    u₁ ~ u₂ → ⌜ u₁ ⌝ ≡ ⌜ u₂ ⌝

  ~confl {⋆} {Γ} {ne us₁} {ne us₂} ns₁≡ns₂ =
    cong ne ns₁≡ns₂
  ~confl {α ⇒ β} {Γ} {u₁} {u₂} u₁~u₂ =
    lam ⌜ val≤ wk u₁ ⟨∙⟩ ne (var zero) ⌝ ≡ lam ⌜ val≤ wk u₂ ⟨∙⟩ ne (var zero) ⌝
      ∋ cong lam (~confl {β} (u₁~u₂ wk (confl-ne→~ refl)))

  confl-ne→~ : ∀ {α Γ} {us₁ us₂ : NeVal Γ α} → 
    ⌜ us₁ ⌝* ≡ ⌜ us₂ ⌝* → ne us₁ ~ ne us₂

  confl-ne→~ {⋆} ns₁≡ns₂ = ns₁≡ns₂
  confl-ne→~ {α ⇒ β} {Γ} {us₁} {us₂} ns₁≡ns₂ η v₁~v₂ =
    confl-ne→~ {β} (cong₂ app q (~confl v₁~v₂))
    where
    open ≡-Reasoning
    q : ⌜ neVal≤ η us₁ ⌝* ≡ ⌜ neVal≤ η us₂ ⌝*
    q = begin
      ⌜ neVal≤ η us₁ ⌝*
        ≡⟨ quote*∘≤ η us₁ ⟩
      neNf≤ η ⌜ us₁ ⌝*
        ≡⟨ cong (neNf≤ η) ns₁≡ns₂ ⟩
      neNf≤ η ⌜ us₂ ⌝*
        ≡⟨ sym $ quote*∘≤ η us₂ ⟩
      ⌜ neVal≤ η us₂ ⌝*
      ∎


mutual

  ~refl : ∀ {α Γ} (u : Val Γ α) → u ~ u

  ~refl {⋆} (ne us) = refl
  ~refl {α ⇒ β} (ne us) η v₁~v₂ =
    confl-ne→~ (cong₂ app refl (~confl v₁~v₂))
  ~refl {α ⇒ β} (lam t ρ) η v₁~v₂ =
    ~cong⟦≡⟧ t (v₁~v₂ ∷ ~~≤ η (~~refl ρ))

  ~~refl : ∀ {Γ Δ} (ρ : Env Γ Δ) → ρ ~~ ρ

  ~~refl [] = []
  ~~refl (u ∷ ρ) = ~refl u ∷ ~~refl ρ


--
-- t ≈ t′ → nf t ≡ nf t′
--

sound : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
  t₁ ≈ t₂ → nf t₁ ≡ nf t₂

sound {α} {Γ} {t₁} {t₂} t₁≈t₂ =
  ~confl (~cong⟦⟧ t₁≈t₂ (~~refl id-env))
