module STLC-Delay.StrongComputability where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.Conversion
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser
open import STLC-Delay.OPEMoreLemmas

--
-- Strong computability.
--

SCV : ∀ {α Γ} (u : Val Γ α) → Set
SCV {⋆} (ne us) = ∃ λ ns →
  readback* us ⇓ ns
  × embNeVal us ≈ embNeNf ns
SCV {α ⇒ β} {Γ} u = ∀ {Β} (η : Β ≤ Γ) (v : Val Β α) (q : SCV v) →
  ∃ λ w → SCV {β} w
    × apply (val≤ η u) v ⇓ w
    × embVal (val≤ η u) ∙ embVal v ≈ embVal w

data SCE {Γ : Ctx} : ∀ {Δ : Ctx} (ρ : Env Γ Δ) → Set where
  [] : SCE []
  _∷_ : ∀ {α Δ} {u : Val Γ α} (p : SCV u) {ρ : Env Γ Δ} (r : SCE ρ) →
    SCE (u ∷ ρ)

--
-- Weakening for SCV & SCE.
--
-- (η : Β ≤ Γ) (p : SCV u) → SCV (val≤ η u)
-- (η : Β ≤ Γ) (r : SCE ρ) → SCE (env≤ η ρ)
--

mutual

  scv≤ :  ∀ {α Γ Β} (η : Β ≤ Γ) (u : Val Γ α) (p : SCV u) →
    SCV (val≤ η u)
  scv≤ {⋆} η (ne us) (ns , ⇓ns , ≈ns) =
    neNf≤ η ns , readback*≤⇓ η us ⇓ns , embNe≤≈ η us ns ≈ns
  scv≤ {α ⇒ β} η u p {Β′} η′ v q
    with p (η′ ● η) v q
  ... | uv , pq , ⇓uv , ≈uv
    rewrite val≤ η′ (val≤ η u) ≡ val≤ (η′ ● η) u ∋ val≤∘ η′ η u
    = uv , pq , ⇓uv , ≈uv

  sce≤ : ∀ {Γ Δ Β} (η : Β ≤ Γ) (ρ : Env Γ Δ) (r : SCE ρ) →
    SCE (env≤ η ρ)
  sce≤ η [] [] = []
  sce≤ η (u ∷ ρ) (p ∷ r) = scv≤ η u p ∷ sce≤ η ρ r


--
-- The fundamental theorem about strong computability:
-- all terms are "strongly computable".
--   ∃ λ u → SCV u × eval t ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u)
--   ∃ λ θ → SCE θ × SCE θ × eval* σ ρ ⇓ θ × (σ ○ embEnv ρ ≈≈ embEnv θ)
--

mutual

  all-scv : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (r : SCE ρ) →
    ∃ λ u → SCV u × eval t ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u)
  all-scv ø  (u ∷ ρ) (p ∷ r) =
    u , p , now⇓ , ≈ø[∷]
  all-scv (f ∙ a) ρ r
    with all-scv f ρ r | all-scv a ρ r
  ... | u , p , ⇓u , ≈u | v , q , ⇓v , ≈v
    with p ≤id v q
  ... | uv , pq , ⇓uv , ≈uv
    rewrite val≤-≤id u
    = uv , pq , bind2⇓ apply ⇓u ⇓v ⇓uv ,
      (begin
        (f ∙ a) [ embEnv ρ ]
          ≈⟨ ≈∙[] ⟩
        f [ embEnv ρ ] ∙ a [ embEnv ρ ]
          ≈⟨ ≈cong∙ ≈u ≈v ⟩
        embVal u ∙ embVal v
          ≈⟨ ≈uv ⟩
        embVal uv
      ∎)
    where open ≈-Reasoning
  all-scv (ƛ t) ρ r =
    lam t ρ , h , now⇓ , ≈refl
    where
    open ≈-Reasoning
    h : SCV (lam t ρ)
    h η u p
      with all-scv t (u ∷ env≤ η ρ) (p ∷ sce≤ η ρ r)
    ... | v , q , ⇓v , ≈v
      = v , q , later⇓ ⇓v ,
        (begin
          (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u
            ≈⟨ ≈βσ ⟩
          t [ embVal u ∷ embEnv (env≤ η ρ) ]
            ≈⟨ ≈v ⟩
          embVal v
        ∎)

  all-scv (t [ σ ]) ρ r
    with all-sce σ ρ r
  ... | θ , cθ , ⇓θ , ≈≈θ
    with all-scv t θ cθ
  ... | u , p , ⇓u , ≈u
    = u , p , bind⇓ (eval t) ⇓θ ⇓u ,
      (begin
        t [ σ ] [ embEnv ρ ]
          ≈⟨ ≈sym ≈[○] ⟩
        t [ σ ○ embEnv ρ ]
          ≈⟨ ≈cong[] ≈refl ≈≈θ ⟩
        t [ embEnv θ ]
          ≈⟨ ≈u ⟩
        embVal u
      ∎)
    where open ≈-Reasoning

  all-sce :  ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ) (r : SCE ρ) →
    ∃ λ θ → SCE θ × eval* σ ρ ⇓ θ × (σ ○ embEnv ρ ≈≈ embEnv θ)
  all-sce ı ρ r =
    ρ , r , now⇓ , ≈≈idl
  all-sce (σ ○ τ) ρ r
    with all-sce τ ρ r
  ... | θ , r′ , ⇓θ , ≈≈θ
    with all-sce σ θ r′
  ... | φ , r′′ , ⇓φ , ≈≈φ
    = φ , r′′ , bind⇓ (eval* σ) (bind⇓ (eval* τ) now⇓ ⇓θ) ⇓φ ,
      (begin
        (σ ○ τ) ○ embEnv ρ
          ≈⟨ ≈≈assoc ⟩
        σ ○ (τ ○ embEnv ρ)
          ≈⟨ ≈≈cong○ ≈≈refl ≈≈θ ⟩
        σ ○ embEnv θ
          ≈⟨ ≈≈φ ⟩
        embEnv φ
      ∎)
    where open ≈≈-Reasoning
  all-sce (t ∷ σ) ρ r
    with all-scv t ρ r | all-sce σ ρ r
  ... | u , p , ⇓u , ≈u | θ , r′ , ⇓θ , ≈≈θ
    = u ∷ θ , p ∷ r′ , bind2⇓ (λ u ρ′ → now (u ∷ ρ′)) ⇓u ⇓θ now⇓ ,
      -- (t ∷ σ) ○ embEnv ρ ≈≈ embVal u ∷ embEnv θ
      (begin
        (t ∷ σ) ○ embEnv ρ
          ≈⟨ ≈≈cons ⟩
        (t [ embEnv ρ ]) ∷ (σ ○ embEnv ρ)
          ≈⟨ ≈≈cong∷ ≈u ≈≈refl ⟩
        embVal u ∷ (σ ○ embEnv ρ)
          ≈⟨ ≈≈cong∷ ≈refl ≈≈θ ⟩
        embVal u ∷ embEnv θ
      ∎)
    where open ≈≈-Reasoning
  all-sce ↑  (u ∷ ρ) (p ∷ r) =
    ρ , r , now⇓ , ≈≈wk
