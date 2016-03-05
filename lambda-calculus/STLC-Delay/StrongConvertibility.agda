module STLC-Delay.StrongConvertibility where

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

--
-- Now we define _≋_ , a relation on values such that
--   u₁ ≋ u₂ →
--     ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × readback u₁ ⇓ n₁ × readback* u₂ ⇓ n₂
--


infix 4 _≋_ _≋≋_

_≋_ : ∀ {α Γ} (u₁ u₂ : Val Γ α) → Set
_≋_ {⋆} (ne us₁) (ne us₂) =
  ∃₂ λ ns₁ ns₂ → ns₁ ≡ ns₂ × readback* us₁ ⇓ ns₁ × readback* us₂ ⇓ ns₂
_≋_ {α ⇒ β} {Γ} f₁ f₂ = ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} →
  u₁ ≋ u₂ → ∃₂ λ w₁ w₂ →
    w₁ ≋ w₂ × apply (val≤ η f₁) u₁ ⇓ w₁ × apply (val≤ η f₂) u₂ ⇓ w₂

data _≋≋_ : ∀ {Γ Δ} (ρ₁ ρ₂ : Env Γ Δ) → Set where
  [] :  ∀ {Γ} →
    _≋≋_ {Γ} [] []
  _∷_ : ∀ {α Γ Δ} {u₁ u₂ : Val Γ α} {ρ₁ ρ₂ : Env Γ Δ} →
    u₁ ≋ u₂ → ρ₁ ≋≋ ρ₂ →
    u₁ ∷ ρ₁ ≋≋ u₂ ∷ ρ₂


mutual

  ≋sym : ∀ {α Γ} {u₁ u₂ : Val Γ α} → u₁ ≋ u₂ → u₂ ≋ u₁

  ≋sym {⋆} {Γ} {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
    ns₂ , ns₁ , sym ns₁≡ns₂ , ⇓ns₂ , ⇓ns₁
  ≋sym {α ⇒ β} {Γ} f₁≋f₂ {B} η {u₁} {u₂} u₁≋u₂
    with f₁≋f₂ η (≋sym u₁≋u₂)
  ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂ =
    w₂ , w₁ , ≋sym w₁≋w₂ , ⇓w₂ , ⇓w₁

  ≋≋sym :  ∀ {Γ Δ} {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ≋≋ ρ₂ → ρ₂ ≋≋ ρ₁

  ≋≋sym [] = []
  ≋≋sym (u₁≋≋u₂ ∷ ρ₁≋≋ρ₂) =
    ≋sym u₁≋≋u₂ ∷ ≋≋sym ρ₁≋≋ρ₂


mutual

  ≋trans : ∀ {α Γ} {u₁ u₂ u₃ : Val Γ α} →
    u₁ ≋ u₂ → u₂ ≋ u₃ → u₁ ≋ u₃
  ≋trans {⋆} {Γ} {ne us₁} {ne us₂} {ne us₃}
    (ns₁ , ns′ , ns₁≡ns′ , ⇓ns₁ , ⇓ns′)
    (ns′′ , ns₃ , ns′′≡ns₃ , ⇓ns′′ , ⇓ns₃)
    rewrite ns′ ≡ ns′′ ∋ ⇓-det ⇓ns′ ⇓ns′′
    = ns₁ , ns₃ , trans ns₁≡ns′ ns′′≡ns₃ , ⇓ns₁ , ⇓ns₃
  ≋trans {α ⇒ β} p q {Β} η {v₁} {v₂} v₁≋v₂
    with p η (≋refl′ v₁≋v₂) | q η v₁≋v₂
  ... | w₁ , w′ , w₁≋w′ , ⇓w₁ , ⇓w′ | w′′ , w₂ , w′′≋w₂ , ⇓w′′ , ⇓w₂
    rewrite w′ ≡ w′′ ∋ ⇓-det ⇓w′ ⇓w′′
    = w₁ , w₂ , ≋trans w₁≋w′ w′′≋w₂ , ⇓w₁ , ⇓w₂

  ≋≋trans : ∀ {Γ Δ} {ρ₁ ρ₂ ρ₃ : Env Γ Δ} →
    ρ₁ ≋≋ ρ₂ → ρ₂ ≋≋ ρ₃ → ρ₁ ≋≋ ρ₃
  ≋≋trans [] ρ₂≋≋ρ₃ = ρ₂≋≋ρ₃
  ≋≋trans (u₁≋u₂ ∷ ρ₁≋≋ρ₂) (u₂≋u₃ ∷ ρ₂≋≋ρ₃) =
    ≋trans u₁≋u₂ u₂≋u₃ ∷ ≋≋trans ρ₁≋≋ρ₂ ρ₂≋≋ρ₃

  ≋refl′ : ∀ {α Γ} {u u′ : Val Γ α} → u ≋ u′ → u ≋ u
  ≋refl′ u≋u′ = ≋trans u≋u′ (≋sym u≋u′)

  ≋≋refl′ : ∀ {Γ Δ} {ρ ρ′ : Env Γ Δ} → ρ ≋≋ ρ′ → ρ ≋≋ ρ
  ≋≋refl′ ρ≋≋ρ′ = ≋≋trans ρ≋≋ρ′ (≋≋sym ρ≋≋ρ′)

--
-- u₁ ≋ u₂ → val≤ η u₁ ≋ val≤ η u₂
-- ρ₁ ≋≋ ρ₂ → env≤ η ρ₁ ≋≋ env≤ η ρ₂
--

≋≤ : ∀ {α Γ Δ} (η : Γ ≤ Δ) {u₁ u₂ : Val Δ α} → u₁ ≋ u₂ →
       val≤ η u₁ ≋ val≤ η u₂
≋≤ {⋆} η {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
  neNf≤ η ns₁ , neNf≤ η ns₂ , cong (neNf≤ η) ns₁≡ns₂ ,
    readback*≤⇓ η us₁ ⇓ns₁ , readback*≤⇓ η us₂ ⇓ns₂
≋≤ {α ⇒ β} η {u₁} {u₂} p {B} η′ {v₁} {v₂} v₁≋v₂
  with p (η′ ● η) v₁≋v₂
... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
  rewrite val≤ η′ (val≤ η u₁) ≡ val≤ (η′ ● η) u₁ ∋ val≤∘ η′ η u₁ |
          val≤ η′ (val≤ η u₂) ≡ val≤ (η′ ● η) u₂ ∋ val≤∘ η′ η u₂
  = w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂

≋≋≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ≋≋ ρ₂ → 
        env≤ η ρ₁ ≋≋ env≤ η ρ₂
≋≋≤ η [] = []
≋≋≤ η (u₁≋u₂ ∷ ρ₁≋≋ρ₂) = ≋≤ η u₁≋u₂ ∷ ≋≋≤ η ρ₁≋≋ρ₂


--
-- "Confluence": u₁ ≋ u₂ →
--     ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × readback u₁ ⇓ n₁ × readback u₂ ⇓ n₂
--

mutual

  ≋confl : ∀ {α Γ} {u₁ u₂ : Val Γ α} (u₁≋u₂ : u₁ ≋ u₂) →
    ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × readback u₁ ⇓ n₁ × readback u₂ ⇓ n₂
  ≋confl {⋆} {Γ} {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
    ne⋆ ns₁ , ne⋆ ns₂ , cong ne⋆ ns₁≡ns₂ , map⇓ ne⋆ ⇓ns₁ , map⇓ ne⋆ ⇓ns₂
  ≋confl {α ⇒ β} {Γ} {u₁} {u₂} u₁≋u₂
    with u₁≋u₂ wk (ne≋ne {us₁ = var zero} now⇓ {var zero} now⇓ refl)
  ... | w₁ , w₂ , w₁≋w₂ , ⇓w₁ , ⇓w₂
    with ≋confl w₁≋w₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    = lam n₁ , lam n₂ , cong lam n₁≡n₂ ,
      later⇓ (map⇓ lam (bind⇓ readback ⇓w₁ ⇓n₁)) ,
      later⇓ (map⇓ lam (bind⇓ readback ⇓w₂ ⇓n₂))

  ne≋ne : ∀ {α Γ}
    {us₁ : NeVal Γ α} {ns₁} (⇓ns₁ : readback* us₁ ⇓ ns₁)
    {us₂ : NeVal Γ α} {ns₂} (⇓ns₂ : readback* us₂ ⇓ ns₂)
    (ns₁≡ns₂ : ns₁ ≡ ns₂) →
    ne us₁ ≋ ne us₂
  ne≋ne {⋆} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂ =
    ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂
  ne≋ne {α ⇒ β} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂
                {Β} η {v₁} {v₂} v₁≋v₂
    with ≋confl v₁≋v₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    with ne (app (neVal≤ η us₁) v₁) ≋ ne (app (neVal≤ η us₂) v₂) ∋
      ne≋ne {β}
        (bind2⇓ (λ ns n → now (app ns n)) (readback*≤⇓ η us₁ ⇓ns₁) ⇓n₁ now⇓)
        (bind2⇓ (λ ns n → now (app ns n)) (readback*≤⇓ η us₂ ⇓ns₂) ⇓n₂ now⇓)
        (cong₂ app (cong (neNf≤ η) ns₁≡ns₂) n₁≡n₂)
  ... | us₁-v₁≋us₂-v₂
    = ne (app (neVal≤ η us₁) v₁) , ne (app (neVal≤ η us₂) v₂) ,
         us₁-v₁≋us₂-v₂ , now⇓ , now⇓
