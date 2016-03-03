module STLC-Delay.Normaliser where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.OPE

mutual

  eval : ∀ {α Γ Δ i} (t : Tm Δ α) (ρ : Env Γ Δ) → Delay i (Val Γ α)
  eval ø (u ∷ ρ) = now u
  eval (f ∙ a) ρ =
    eval f ρ >>= (λ u → eval a ρ >>= apply u)
  eval (ƛ t) ρ = now (lam t ρ)
  eval (t [ σ ]) ρ =
    eval* σ ρ >>= eval t

  eval* : ∀ {Β Γ Δ i} (σ : Sub Β Γ) (ρ : Env Δ Β) → Delay i (Env Δ Γ)
  eval* ı ρ = now ρ
  eval* (σ ○ τ) ρ =
    eval* τ ρ >>= eval* σ
  eval* (t ∷ σ) ρ =
    eval t ρ >>= (λ u → eval* σ ρ >>= (λ ρ′ → now (u ∷ ρ′)))
  eval* ↑ (u ∷ ρ) = now ρ

  apply : ∀ {α β Γ i} (u : Val Γ (α ⇒ β)) (v : Val Γ α) →
    Delay i (Val Γ β)
  apply (ne us) v = now (ne (app us v))
  apply (lam t ρ) v = later (beta t ρ v)

  beta : ∀  {α β Γ Δ i} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) (v : Val Γ α) →
    ∞Delay i (Val Γ β)
  force (beta t ρ v) = eval t (v ∷ ρ)

mutual

  readback : ∀ {α Γ i} (u : Val Γ α) → Delay i (Nf Γ α)
  readback {⋆} (ne us) = ne⋆ <$> readback* us
  readback {α ⇒ β} u = lam <$> later (eta u)

  readback* : ∀ {α Γ i} (u : NeVal Γ α) → Delay i (NeNf Γ α)
  readback* (var x) = now (var x)
  readback* (app us u) =
    readback* us >>= (λ ns → readback u >>= (λ n → now (app ns n)))

  eta : ∀ {α β Γ i} (u : Val Γ (α ⇒ β)) → ∞Delay i (Nf (α ∷ Γ) β)
  force (eta u) = apply (val≤ wk u) (ne (var zero)) >>= readback

--
-- ∀ {α Γ} (t : Tm Γ α) → Delay ∞ (Nf Γ α)
--

nf? : ∀ {α Γ} (t : Tm Γ α) → Delay ∞ (Nf Γ α)
nf? {α} {Γ} t = eval t (id-env Γ) >>= readback
