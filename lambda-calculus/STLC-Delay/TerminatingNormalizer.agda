module STLC-Delay.TerminatingNormalizer where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser
open import STLC-Delay.OPEMoreLemmas
open import STLC-Delay.StrongComputability

--
-- Reification: from values to normal forms.
--

mutual

  reify : ∀ {α Γ} (u : Val Γ α) (p : SCV u) → readback u ⇓
  reify {⋆} (ne us) (ns , ⇓ns) =
    ne⋆ ns , map⇓ ne⋆ ⇓ns
  reify {α ⇒ β} {Γ} u p
    with reflect (var (zero {α} {Γ})) (var zero , now⇓)
  ... | q
    with p wk (ne (var zero)) q
  ... | w , r , ⇓w
    with reify w r
  ... | n , ⇓n
    = lam n ,
      later⇓ (bind⇓ (λ n → now (lam n)) (bind⇓ readback ⇓w ⇓n) now⇓)

  reflect : ∀ {α Γ} (us : NeVal Γ α) (us⇓ : readback* us ⇓) →
    SCV (ne us)
  reflect {⋆} us us⇓ = us⇓
  reflect {α ⇒ β} us (ns , ⇓ns) {Β} η u q
    with readback*≤⇓ η us ⇓ns | reify u q
  ... | ⇓ns′ | n , ⇓n
    = ne (app (neVal≤ η us) u) ,
      reflect {β} (app (neVal≤ η us) u)
                  (app (neNf≤ η ns) n ,
                    bind2⇓ (λ ns′ n′ → now (app ns′ n′)) ⇓ns′ ⇓n now⇓) ,
      now⇓


-- SCV (ne (var x))

scv-var : ∀ {α Γ} (x : Var Γ α) → SCV (ne (var x))
scv-var x = reflect (var x) (var x , now⇓)

-- SCE (id-env Γ)

sce-id-env : ∀ Γ → SCE (id-env Γ)
sce-id-env [] = []
sce-id-env (γ ∷ Γ) = scv-var zero ∷ sce≤ wk (id-env Γ) (sce-id-env Γ)

--
-- Now we get a normalizer that always terminates.
--

norm : ∀ {α Γ} (t : Tm Γ α) → ∃ λ n → nf t ⇓ n
norm {α} {Γ} t
  with all-sc t (id-env Γ) (sce-id-env Γ)
... | u , p , ⇓u
  with reify u p
... | n , ⇓n
  = n , bind⇓ readback ⇓u ⇓n
