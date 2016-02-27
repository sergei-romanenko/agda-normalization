module STLC-Delay.StrongComputability where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser
open import STLC-Delay.OPEMoreLemmas

mutual

  SC : ∀ {α Γ} (u? : Delay ∞ (Val Γ α)) → Set
  SC u? = ∃ λ u → SCV u × u? ⇓ u

  SCV : ∀ {α Γ} (u : Val Γ α) → Set
  SCV {⋆} (ne us) = ∃ λ ns → readback* us ⇓ ns
  SCV {α ⇒ β} {Γ} u = ∀ {Β} (η : Β ≤ Γ) (v : Val Β α) (q : SCV v) →
    SC {β} (apply (val≤ η u) v)

--infixr 5 _∷_

data SCE {Γ : Ctx} : ∀ {Δ : Ctx} (ρ : Env Γ Δ) → Set where
  [] : SCE []
  _∷_ : ∀ {α Δ} {u : Val Γ α} (p : SCV u) {ρ : Env Γ Δ} (r : SCE ρ) →
    SCE (u ∷ ρ)

mutual

  scv≤ :  ∀ {α Γ Β} (η : Β ≤ Γ) (u : Val Γ α) (p : SCV u) →
    SCV (val≤ η u)
  scv≤ {⋆} η (ne us) (ns , ⇓ns) =
    neNf≤ η ns , readback*≤⇓ η us ⇓ns
  scv≤ {α ⇒ β} η u p {Β′} η′ v q
    with p (η′ ● η) v q
  ... | uv , pq , ⇓uv
    rewrite val≤ η′ (val≤ η u) ≡ val≤ (η′ ● η) u ∋ val≤∘ η′ η u
    = uv , pq , ⇓uv

  sce≤ : ∀ {Γ Δ Β} (η : Β ≤ Γ) (ρ : Env Γ Δ) (r : SCE ρ) →
    SCE (env≤ η ρ)
  sce≤ η [] [] = []
  sce≤ η (u ∷ ρ) (p ∷ r) = scv≤ η u p ∷ sce≤ η ρ r

mutual

  all-sc : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (r : SCE ρ) →
    SC (eval t ρ)
  all-sc ø (u ∷ ρ) (p ∷ r) =
    u , p , now⇓
  all-sc (f ∙ a) ρ r
    with all-sc f ρ r | all-sc a ρ r
  ... | u , p , ⇓u | v , q , ⇓v
    with p ≤id v q
  ... | uv , pq , ⇓uv
    rewrite val≤-≤id u
    = uv , pq , bind2⇓ apply ⇓u ⇓v ⇓uv
  all-sc (ƛ t) ρ r =
    lam t ρ , h , now⇓
    where
    h : SCV (lam t ρ)
    h η u p
      with all-sc t (u ∷ env≤ η ρ) (p ∷ sce≤ η ρ r)
    ... | v , q , ⇓v
      = v , q , later⇓ ⇓v
  all-sc (t [ σ ]) ρ r
    with all-sce σ ρ r
  ... | θ , cθ , ⇓θ
    with all-sc t θ cθ
  ... | u , p , ⇓u
    = u , p , bind⇓ (eval t) ⇓θ ⇓u

  all-sce :  ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ) (r : SCE ρ) →
    ∃ λ θ → SCE θ × eval* σ ρ ⇓ θ
  all-sce ı ρ r =
    ρ , r , now⇓
  all-sce (σ ○ τ) ρ r
    with all-sce τ ρ r
  ... | θ , r′ , ⇓θ
    with all-sce σ θ r′
  ... | φ , r′′ , ⇓φ
    = φ , r′′ , bind⇓ (eval* σ) (bind⇓ (eval* τ) now⇓ ⇓θ) ⇓φ
  all-sce (t ∷ σ) ρ r
    with all-sc t ρ r | all-sce σ ρ r
  ... | u , p , ⇓u | θ , r′ , ⇓θ
    = u ∷ θ , p ∷ r′ , bind2⇓ (λ u₁ ρ′ → now (u₁ ∷ ρ′)) ⇓u ⇓θ now⇓
  all-sce ↑ (u ∷ ρ) (p ∷ r) =
    ρ , r , now⇓
