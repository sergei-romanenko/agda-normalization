module STLC-Delay.Soundness where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.Conversion
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser
open import STLC-Delay.OPEMoreLemmas
open import STLC-Delay.StrongComputability
open import STLC-Delay.TerminatingNormalizer
open import STLC-Delay.StrongConvertibility

--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
-- (Normalisation takes convertible terms to identical normal forms.)
--

--
-- ρ₁ ≋≋ ρ₂ →
--     ∃₂ λ u₁ u₂ → u₁ ≋ u₂ × (eval t ρ₁ ⇓ u₁) × (eval t ρ₂ ⇓ u₂)
-- ρ₁ ≋≋ ρ₂ →
--     ∃₂ λ θ₁ θ₂ → θ₁ ≋≋ θ₂ × (eval* σ ρ₁ ⇓ θ₁) × (eval* σ ρ₂ ⇓ θ₂)

mutual

  ≡eval : ∀ {α Γ Δ} (t : Tm Δ α)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁≋≋ρ₂ : ρ₁ ≋≋ ρ₂) →
    ∃₂ λ u₁ u₂ → u₁ ≋ u₂ × (eval t ρ₁ ⇓ u₁) × (eval t ρ₂ ⇓ u₂)
  ≡eval ø {u₁ ∷ ρ₁} {u₂ ∷ ρ₂} (u₁≋u₂ ∷ ρ₁≋≋ρ₂) =
    u₁ , u₂ , u₁≋u₂ , now⇓ , now⇓
  ≡eval (f ∙ a) ρ₁≋≋ρ₂
    with ≡eval f ρ₁≋≋ρ₂ | ≡eval a ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
    with u₁≋u₂ ≤id v₁≋v₂
  ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁≋w₂ ,
      bind2⇓ apply ⇓u₁ ⇓v₁ ⇓w₁ , bind2⇓ apply ⇓u₂ ⇓v₂ ⇓w₂
  ≡eval {α ⇒ β} {Γ} (ƛ t) {ρ₁} {ρ₂} ρ₁≋≋ρ₂ =
    lam t ρ₁ , lam t ρ₂ , h , now⇓ , now⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} → u₁ ≋ u₂ →
          ∃₂ λ w₁ w₂ → w₁ ≋ w₂
            × later (beta t (env≤ η ρ₁) u₁) ⇓ w₁
            × later (beta t (env≤ η ρ₂) u₂) ⇓ w₂
    h {Β} η u₁≋u₂
      with ≡eval t (u₁≋u₂ ∷ ≋≋≤ η ρ₁≋≋ρ₂)
    ... | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
      = v₁ , v₂ , v₁≋v₂ , later⇓ ⇓v₁ , later⇓ ⇓v₂
  ≡eval (t [ σ ]) ρ₁≋≋ρ₂
    with ≡eval* σ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval t θ₁≋≋θ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁≋u₂ ,
      bind⇓ (eval t) ⇓θ₁ ⇓u₁ , bind⇓ (eval t) ⇓θ₂ ⇓u₂

  ≡eval* : ∀ {Γ Δ Δ′} (σ : Sub Δ Δ′)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁≋≋ρ₂ : ρ₁ ≋≋ ρ₂) →
    ∃₂ λ θ₁ θ₂ → θ₁ ≋≋ θ₂ × (eval* σ ρ₁ ⇓ θ₁) × (eval* σ ρ₂ ⇓ θ₂)

  ≡eval* ı {ρ₁} {ρ₂} ρ₁≋≋ρ₂ =
    ρ₁ , ρ₂ , ρ₁≋≋ρ₂ , now⇓ , now⇓
  ≡eval* (σ ○ τ) ρ₁≋≋ρ₂
    with ≡eval* τ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval* σ θ₁≋≋θ₂
  ... | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    = φ₁ , φ₂ , φ₁≋≋φ₂ ,
      bind⇓ (eval* σ) ⇓θ₁ ⇓φ₁ , bind⇓ (eval* σ) ⇓θ₂ ⇓φ₂
  ≡eval* (t ∷ σ) ρ₁≋≋ρ₂
    with ≡eval t ρ₁≋≋ρ₂ | ≡eval* σ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ ∷ θ₁ , u₂ ∷ θ₂ , u₁≋u₂ ∷ θ₁≋≋θ₂ ,
      bind2⇓ (λ u ρ → now (u ∷ ρ)) ⇓u₁ ⇓θ₁ now⇓ ,
      bind2⇓ (λ u ρ → now (u ∷ ρ)) ⇓u₂ ⇓θ₂ now⇓
  ≡eval* ↑ {u₁ ∷ ρ₁} {u₂ ∷ ρ₂} (u₁≋u₂ ∷ ρ₁≋≋ρ₂) =
    ρ₁ , ρ₂ , ρ₁≋≋ρ₂ , now⇓ , now⇓


--
-- t₁ ≈ t₂ → ρ₁ ~~ ρ₂ →
--     ∃₂ λ u₁ u₂ → u₁ ~ u₂ × ⟦ t₁ ⟧ ρ₁ ⇓ u₁ × ⟦ t₂ ⟧ ρ₂ ⇓ u₂
--
-- σ₁ ≈≈ σ₂ → ρ₁ ~~ ρ₂ →
--     ∃₂ λ θ₁ θ₂ → θ₁ ~~ θ₂ × ⟦ σ₁ ⟧* ρ₁ ⇓ θ₁ × ⟦ σ₂ ⟧* ρ₂ ⇓ θ₂
--

mutual

  ≈eval : ∀ {α Γ Δ}
    {t₁ t₂ : Tm Δ α} (t₁≈t₂ : t₁ ≈ t₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁≋≋ρ₂ : ρ₁ ≋≋ ρ₂) →
    ∃₂ λ u₁ u₂ → u₁ ≋ u₂ × eval t₁ ρ₁ ⇓ u₁ × eval t₂ ρ₂ ⇓ u₂
  ≈eval {t₁ = t} ≈refl ρ₁≋≋ρ₂ =
    ≡eval t ρ₁≋≋ρ₂
  ≈eval (≈sym t₁≈t₂) ρ₁≋≋ρ₂
    with ≈eval t₁≈t₂ (≋≋sym ρ₁≋≋ρ₂)
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₂ , u₁ , ≋sym u₁≋u₂ , ⇓u₂ , ⇓u₁
  ≈eval (≈trans t₁≈t₂ t₂≈t₃) ρ₁≋≋ρ₂
    with ≈eval t₁≈t₂ (≋≋refl′ ρ₁≋≋ρ₂) | ≈eval t₂≈t₃ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
    rewrite u₂ ≡ v₁ ∋ ⇓-det ⇓u₂ ⇓v₁
    = u₁ , v₂ , ≋trans u₁≋u₂ v₁≋v₂ , ⇓u₁ , ⇓v₂
  ≈eval  {t₁ = f₁ ∙ a₁} {t₂ = f₂ ∙ a₂} (≈cong∙ f₁≈f₂ a₁≈a₂) ρ₁≋≋ρ₂
    with ≈eval f₁≈f₂ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    with ≈eval a₁≈a₂ ρ₁≋≋ρ₂
  ... | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
    with u₁≋u₂ ≤id v₁≋v₂
  ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁≋w₂ ,
      bind2⇓ apply ⇓u₁ ⇓v₁ ⇓w₁ , bind2⇓ apply ⇓u₂ ⇓v₂ ⇓w₂
  ≈eval {t₁ = t₁ [ σ₁ ]} {t₂ = t₂ [ σ₂ ]} (≈cong[] t₁≈t₂ σ₁≈≈σ₂) ρ₁≋≋ρ₂
    with ≈eval* σ₁≈≈σ₂ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≈eval t₁≈t₂ θ₁≋≋θ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁≋u₂ ,
      bind⇓ (eval t₁) ⇓θ₁ ⇓u₁ , bind⇓ (eval t₂) ⇓θ₂ ⇓u₂
  ≈eval {t₁ = (ƛ t₁)} {t₂ = (ƛ t₂)} (≈congƛ t₁≈t₂) {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    = lam t₁ ρ₁ , lam t₂ ρ₂ , h , now⇓ , now⇓
    where
    h : lam t₁ ρ₁ ≋ lam t₂ ρ₂
    h {Β} η {u₁} {u₂} u₁≋u₂
      with ≈eval t₁≈t₂ (u₁≋u₂ ∷ ≋≋≤ η ρ₁≋≋ρ₂)
    ... | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
      = v₁ , v₂ , v₁≋v₂ ,
        later⇓ ⇓v₁ , later⇓ ⇓v₂
  ≈eval {t₁ = ø [ t ∷ σ ]} ≈ø[∷] {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval t ρ₁≋≋ρ₂ | ≡eval* σ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ , u₂ , u₁≋u₂ ,
      --[]⇓ (∷⇓ ⇓u₁ ⇓θ₁) ø⇓ , ⇓u₂
      subst~⇓ (~sym h) (bind2⇓ (λ u ρ → now u) ⇓u₁ ⇓θ₁ now⇓) , ⇓u₂
    where
    open ~-Reasoning
    h = begin
      (eval t ρ₁ >>= (λ u → eval* σ ρ₁ >>= (λ ρ → now (u ∷ ρ))) >>= eval ø)
        ≈⟨ bind-assoc (eval t ρ₁) ⟩
      (eval t ρ₁ >>= λ u → (eval* σ ρ₁ >>= (λ ρ → now (u ∷ ρ))) >>= eval ø)
        ≈⟨ bind-cong-r (eval t ρ₁) (λ u → bind-assoc (eval* σ ρ₁)) ⟩
      (eval t ρ₁ >>= λ u → eval* σ ρ₁ >>= λ ρ → now (u ∷ ρ) >>= eval ø)
        ≡⟨⟩
      (eval t ρ₁ >>= λ u → eval* σ ρ₁ >>= λ ρ → now u)
      ∎
  ≈eval {t₁ = t [ ı ]} ≈[ı] ρ₁≋≋ρ₂
    with ≡eval t ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
  ≈eval {t₁ = t [ σ ○ τ ]} ≈[○] {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval* τ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval* σ θ₁≋≋θ₂
  ... | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    with ≡eval t φ₁≋≋φ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁≋u₂ ,
      bind⇓ (eval t) (bind⇓ (eval* σ) ⇓θ₁ ⇓φ₁) ⇓u₁ ,
      subst~⇓ (bind-assoc (eval* τ ρ₂))
              (bind⇓ (eval t) (bind⇓ (eval* σ) ⇓θ₂ ⇓φ₂) ⇓u₂)
  ≈eval {α ⇒ β} {Γ} {t₁ = (ƛ t) [ σ ]} ≈ƛ[] {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval* σ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval (ƛ t) θ₁≋≋θ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , lam (t [ ø ∷ (σ ○ ↑) ]) ρ₂ , h ,
      bind⇓ (now ∘ lam t) ⇓θ₁ ⇓u₁ , now⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {v₁ v₂ : Val Β α} (v₁≋v₂ : v₁ ≋ v₂) →
          ∃₂ λ w₁ w₃ → w₁ ≋ w₃
               × apply (val≤ η u₁) v₁ ⇓ w₁
               × apply (lam (t [ ø ∷ (σ ○ ↑) ]) (env≤ η ρ₂)) v₂ ⇓ w₃
    h {Β} η {v₁} {v₂} v₁≋v₂
      with ≡eval t (v₁≋v₂ ∷ ≋≋≤ η θ₁≋≋θ₂)
    ... | y₁ , y₂ , y₁≋y₂ , ⇓y₁ , ⇓y₂
      rewrite val≤ η u₁ ≡ lam t (env≤ η θ₁)
                   ∋ ⇓-det (eval⇓≤ η (ƛ t) θ₁ ⇓u₁) now⇓
      = y₁ , y₂ , y₁≋y₂ ,
        later⇓ ⇓y₁ ,
        later⇓ (bind⇓ (eval t)
                      (bind⇓ (λ ρ′ → now (v₂ ∷ ρ′))
                            (eval*⇓≤ η σ ρ₂ ⇓θ₂) now⇓) ⇓y₂)
  ≈eval {t₁ = (f ∙ a) [ σ ]} ≈∙[] {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval* σ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval f θ₁≋≋θ₂ | ≡eval a θ₁≋≋θ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
    with u₁≋u₂ ≤id v₁≋v₂
  ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁≋w₂ ,
      bind⇓ (λ ρ → eval f ρ >>= λ u → eval a ρ >>= apply u)
            ⇓θ₁ (bind2⇓ apply ⇓u₁ ⇓v₁ ⇓w₁) ,
      bind2⇓ apply (bind⇓ (eval f) ⇓θ₂ ⇓u₂) (bind⇓ (eval a) ⇓θ₂ ⇓v₂) ⇓w₂
  ≈eval {t₁ = (ƛ t) [ σ ] ∙ a} ≈βσ {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval a ρ₁≋≋ρ₂ | ≡eval* σ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval t (u₁≋u₂ ∷ θ₁≋≋θ₂)
  ... | v₁ , v₂ , v₁≋v₂ , ⇓v₁ , ⇓v₂
    = v₁ , v₂ , v₁≋v₂ ,
      subst~⇓ (~sym h1)
              (bind2⇓ (λ ρ u → later (beta t ρ u)) ⇓θ₁ ⇓u₁ (later⇓ ⇓v₁)) ,
      subst~⇓ (~sym h2) (bind2⇓ (λ u ρ → eval t (u ∷ ρ)) ⇓u₂ ⇓θ₂ ⇓v₂)
    where
    open ~-Reasoning
    h1 = begin
      ((eval* σ ρ₁ >>= (λ ρ → now (lam t ρ))) >>= λ u → eval a ρ₁ >>= apply u)
        ≈⟨ bind-assoc (eval* σ ρ₁) ⟩
      (eval* σ ρ₁ >>= λ ρ → now (lam t ρ) >>= λ u → eval a ρ₁ >>= apply u)
        ≡⟨⟩
      (eval* σ ρ₁ >>= λ ρ → eval a ρ₁ >>= apply (lam t ρ))
      ∎
    h2 = begin
      ((eval a ρ₂ >>= (λ u → eval* σ ρ₂ >>= λ ρ → now (u ∷ ρ))) >>= eval t)
        ≈⟨ bind-assoc (eval a ρ₂) ⟩
      (eval a ρ₂ >>= λ u → (eval* σ ρ₂ >>= λ ρ → now (u ∷ ρ)) >>= eval t)
        ≈⟨ bind-cong-r (eval a ρ₂) (λ u → bind-assoc (eval* σ ρ₂)) ⟩
      (eval a ρ₂ >>= λ u → eval* σ ρ₂ >>= λ ρ → now (u ∷ ρ) >>= eval t)
        ≡⟨⟩
      (eval a ρ₂ >>= λ u → eval* σ ρ₂ >>= λ ρ → eval t (u ∷ ρ))
      ∎
  ≈eval {α ⇒ β} {Γ} {Δ} {t₂ = ƛ (t [ ↑ ] ∙ ø)} ≈η {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval t ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂
    = u₁ , lam (t [ ↑ ] ∙ ø) ρ₂ , h , ⇓u₁ , now⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {v₁ v₂ : Val Β α} (v₁≋v₂ : v₁ ≋ v₂) →
          ∃₂ λ w₁ w₃ → w₁ ≋ w₃
               × apply (val≤ η u₁) v₁ ⇓ w₁
               × apply (val≤ η (lam (t [ ↑ ] ∙ ø) ρ₂)) v₂ ⇓ w₃
    h {Β} η {v₁} {v₂} v₁≋v₂
      with ≋≤ η {u₁} u₁≋u₂ {Β} ≤id v₁≋v₂
    ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
      rewrite val≤ ≤id (val≤ η u₁) ≡ val≤ η u₁ ∋ val≤-≤id (val≤ η u₁) |
              val≤ ≤id (val≤ η u₂) ≡ val≤ η u₂ ∋ val≤-≤id (val≤ η u₂)
      = w₁ , w₂ , w₁≋w₂ , ⇓w₁ , g
      where
      g : apply (lam (t [ ↑ ] ∙ ø) (env≤ η ρ₂)) v₂ ⇓ w₂
      g = later⇓ (bind⇓ (λ u → apply u v₂) (eval⇓≤ η t ρ₂ ⇓u₂) ⇓w₂)

  ≈eval* : ∀ {Γ Δ Δ′}
    {σ₁ σ₂ : Sub Δ Δ′} (σ₁≈≈σ₂ : σ₁ ≈≈ σ₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁≋≋ρ₂ : ρ₁ ≋≋ ρ₂) →
    ∃₂ λ θ₁ θ₂ → θ₁ ≋≋ θ₂ × eval* σ₁ ρ₁ ⇓ θ₁ × eval* σ₂ ρ₂ ⇓ θ₂

  ≈eval* {σ₁ = σ} ≈≈refl ρ₁≋≋ρ₂ =
    ≡eval* σ ρ₁≋≋ρ₂
  ≈eval* (≈≈sym σ₁≈≈σ₂) ρ₁≋≋ρ₂
    with ≈eval* σ₁≈≈σ₂ (≋≋sym ρ₁≋≋ρ₂)
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₂ , θ₁ , ≋≋sym θ₁≋≋θ₂ , ⇓θ₂ , ⇓θ₁
  ≈eval* (≈≈trans σ₁≈≈σ₂ σ₂≈≈σ₃) ρ₁≋≋ρ₂
    with ≈eval* σ₁≈≈σ₂ (≋≋refl′ ρ₁≋≋ρ₂) | ≈eval* σ₂≈≈σ₃ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂ | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    rewrite θ₂ ≡ φ₁ ∋ ⇓-det ⇓θ₂ ⇓φ₁
    = θ₁ , φ₂ , ≋≋trans θ₁≋≋θ₂ φ₁≋≋φ₂ , ⇓θ₁ , ⇓φ₂
  ≈eval* {σ₁ = σ₁ ○ τ₁} {σ₂ = σ₂ ○ τ₂} (≈≈cong○ σ₁≈≈σ₂ τ₁≈≈τ₂) ρ₁≋≋ρ₂
    with ≈eval* τ₁≈≈τ₂ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≈eval* σ₁≈≈σ₂ θ₁≋≋θ₂
  ... | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    = φ₁ , φ₂ , φ₁≋≋φ₂ ,
      bind⇓ (eval* σ₁) ⇓θ₁ ⇓φ₁ , bind⇓ (eval* σ₂) ⇓θ₂ ⇓φ₂
  ≈eval* (≈≈cong∷ t₁≈t₂ σ₁≈≈σ₂) ρ₁≋≋ρ₂
    with ≈eval t₁≈t₂ ρ₁≋≋ρ₂ | ≈eval* σ₁≈≈σ₂ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ ∷ θ₁ , u₂ ∷ θ₂ , u₁≋u₂ ∷ θ₁≋≋θ₂ ,
      bind2⇓ (λ u ρ → now (u ∷ ρ)) ⇓u₁ ⇓θ₁ now⇓ ,
      bind2⇓ (λ u ρ → now (u ∷ ρ)) ⇓u₂ ⇓θ₂ now⇓
  ≈eval* {σ₁ = (σ₁ ○ σ₂) ○ σ₃} ≈≈assoc {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval* σ₃ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval* σ₂ θ₁≋≋θ₂
  ... | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    with ≡eval* σ₁ φ₁≋≋φ₂
  ... | ψ₁ , ψ₂ , ψ₁≋≋ψ₂ , ⇓ψ₁ , ⇓ψ₂
    = ψ₁ , ψ₂ , ψ₁≋≋ψ₂ ,
      bind⇓ (λ ρ → eval* σ₂ ρ >>= eval* σ₁) ⇓θ₁ (bind⇓ (eval* σ₁) ⇓φ₁ ⇓ψ₁) ,
      bind⇓ (eval* σ₁) (bind⇓ (eval* σ₂) ⇓θ₂ ⇓φ₂) ⇓ψ₂
  ≈eval* {σ₁ = ı ○ σ} ≈≈idl ρ₁≋≋ρ₂
    with ≡eval* σ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁≋≋θ₂ , bind⇓ now ⇓θ₁ now⇓ , ⇓θ₂
  ≈eval* {σ₁ = σ ○ ı} ≈≈idr ρ₁≋≋ρ₂
    with ≡eval* σ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
  ≈eval* {σ₁ = ↑ ○ (t ∷ σ)} ≈≈wk {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval t ρ₁≋≋ρ₂ | ≡eval* σ ρ₁≋≋ρ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁≋≋θ₂ ,
    subst~⇓ (~sym h) (bind2⇓ (λ u ρ → now ρ) ⇓u₁ ⇓θ₁ now⇓) , ⇓θ₂
    where
    open ~-Reasoning
    h = begin
      (eval t ρ₁ >>= (λ u → eval* σ ρ₁ >>= (λ ρ′ → now (u ∷ ρ′))) >>= eval* ↑)
        ≈⟨ bind-assoc (eval t ρ₁) ⟩
      (eval t ρ₁ >>= λ u → eval* σ ρ₁ >>= (λ ρ′ → now (u ∷ ρ′)) >>= eval* ↑)
        ≈⟨ bind-cong-r (eval t ρ₁) (λ u → bind-assoc (eval* σ ρ₁)) ⟩
      (eval t ρ₁ >>= λ u → eval* σ ρ₁ >>= λ ρ′ → now (u ∷ ρ′) >>= eval* ↑)
        ≡⟨⟩
      (eval t ρ₁ >>= λ u → eval* σ ρ₁ >>= now)
      ∎
  ≈eval* {σ₁ = (t ∷ σ) ○ τ} ≈≈cons {ρ₁} {ρ₂} ρ₁≋≋ρ₂
    with ≡eval* τ ρ₁≋≋ρ₂
  ... | θ₁ , θ₂ , θ₁≋≋θ₂ , ⇓θ₁ , ⇓θ₂
    with ≡eval t θ₁≋≋θ₂ | ≡eval* σ θ₁≋≋θ₂
  ... | u₁ , u₂ , u₁≋u₂ , ⇓u₁ , ⇓u₂ | φ₁ , φ₂ , φ₁≋≋φ₂ , ⇓φ₁ , ⇓φ₂
    = u₁ ∷ φ₁ , u₂ ∷ φ₂ , u₁≋u₂ ∷ φ₁≋≋φ₂ ,
      bind⇓ (λ θ → eval t θ >>= λ u → eval* σ θ >>= λ ρ → now (u ∷ ρ))
            ⇓θ₁ (bind2⇓ (λ u ρ → now (u ∷ ρ)) ⇓u₁ ⇓φ₁ now⇓) ,
      bind2⇓ (λ u ρ → now (u ∷ ρ))
                (bind⇓ (eval t) ⇓θ₂ ⇓u₂) (bind⇓ (eval* σ) ⇓θ₂ ⇓φ₂) now⇓
  ≈eval* ≈≈id∷ (_∷_ {u₁ = u₁} {u₂} {ρ₁} {ρ₂} u₁≋u₂ ρ₁≋≋ρ₂)
    = u₁ ∷ ρ₁ , u₂ ∷ ρ₂ , u₁≋u₂ ∷ ρ₁≋≋ρ₂ , now⇓ , now⇓


-- id-env ≋≋ id-env

≋≋refl-id-env : ∀ {Γ} → id-env {Γ} ≋≋ id-env
≋≋refl-id-env {[]} = []
≋≋refl-id-env {γ ∷ Γ} =
  ne≋ne now⇓ now⇓ refl ∷ ≋≋≤ wk ≋≋refl-id-env


--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
--

sound : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
  t₁ ≈ t₂ → nf t₁ ≡ nf t₂

sound {α} {Γ} {t₁} {t₂} t₁≈t₂
  with all-scv t₁ id-env sce-id-env | all-scv t₂ id-env sce-id-env
... | u₁ , p₁ , ⇓u₁ , ≈u₁ | u₂ , p₂ , ⇓u₂ , ≈u₂
  with reify u₁ p₁ | reify u₂ p₂
... | m₁ , ⇓m₁ , ≈m₁ | m₂ , ⇓m₂ , ≈m₂
  with ≈eval t₁≈t₂ ≋≋refl-id-env
... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
  with ≋confl w₁≋w₂
... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
  rewrite u₁ ≡ w₁ ∋ ⇓-det ⇓u₁ ⇓w₁ | u₂ ≡ w₂ ∋ ⇓-det ⇓u₂ ⇓w₂ |
          m₁ ≡ n₁ ∋ ⇓-det ⇓m₁ ⇓n₁ | m₂ ≡ n₂ ∋ ⇓-det ⇓m₂ ⇓n₂
  = n₁≡n₂
