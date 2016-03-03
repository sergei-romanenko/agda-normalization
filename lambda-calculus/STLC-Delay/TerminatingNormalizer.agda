module STLC-Delay.TerminatingNormalizer where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.Conversion
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser
open import STLC-Delay.OPEMoreLemmas
open import STLC-Delay.StrongComputability

--
-- Reification: from values to normal forms.
--

mutual

  reify : ∀ {α Γ} (u : Val Γ α) (p : SCV u) →
    ∃ λ n → readback u ⇓ n × embVal u ≈ embNf n
  reify {⋆} (ne us) (ns , ⇓ns , ≈ns) =
    ne⋆ ns , map⇓ ne⋆ ⇓ns , ≈ns
  reify {α ⇒ β} {Γ} u p
    with reflect {α} (var (zero {α} {Γ})) (var zero) now⇓ ≈refl
  ... | q
    with p wk (ne (var zero)) q
  ... | w , r , ⇓w , ≈w
    with reify {β} w r
  ... | n , ⇓n , ≈n
    = lam n ,
      later⇓ (map⇓ lam (bind⇓ readback ⇓w ⇓n)) ,
      (begin
        embVal u
          ≈⟨ ≈η ⟩
        ƛ embVal u [ ↑ ] ∙ ø
          ≈⟨ ≈congƛ (≈cong∙ (≈sym (embVal∘wk u)) ≈refl) ⟩
        ƛ embVal (val≤ wk u) ∙ ø
          ≈⟨ ≈congƛ ≈w ⟩
        ƛ embVal w
          ≈⟨ ≈congƛ ≈n ⟩
        ƛ embNf n
          ≡⟨⟩
        embNf (lam n)
      ∎)
    where open ≈-Reasoning

  reflect : ∀ {α Γ} (us : NeVal Γ α) (ns : NeNf Γ α)
    (⇓ns : readback* us ⇓ ns) (≈ns : embNeVal us ≈ embNeNf ns) →
    SCV (ne us)
  reflect {⋆} us ns ⇓ns ≈ns =
    ns , ⇓ns , ≈ns
  reflect {α ⇒ β} us ns ⇓ns ≈ns {Β} η u q
    with readback*≤⇓ η us ⇓ns | reify u q
  ... | ⇓ns′ | n , ⇓n , ≈n
    = (ne (app (neVal≤ η us) u)) ,
      reflect {β} (app (neVal≤ η us) u) (app (neNf≤ η ns) n)
              (bind2⇓ (λ ns′ n′ → now (app ns′ n′)) ⇓ns′ ⇓n now⇓)
              (begin
                 embNeVal (neVal≤ η us) ∙ embVal u
                   ≈⟨ ≈cong∙ (embNe≤≈ η us ns ≈ns) ≈n ⟩
                 embNeNf (neNf≤ η ns) ∙ embNf n
              ∎) ,
      now⇓ , ≈refl
    where open ≈-Reasoning

-- SCV (ne (var x))

scv-var : ∀ {α Γ} (x : Var Γ α) → SCV (ne (var x))
scv-var x = reflect (var x) (var x) now⇓ ≈refl

-- SCE (id-env Γ)

sce-id-env : ∀ Γ → SCE (id-env Γ)
sce-id-env [] = []
sce-id-env (γ ∷ Γ) = scv-var zero ∷ sce≤ wk (id-env Γ) (sce-id-env Γ)

--
-- Now we get a normalizer that always terminates.
--

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf {α} {Γ} t
  with all-scv t (id-env Γ) (sce-id-env Γ)
... | u , p , ⇓u , ≈u
  with reify u p
... | n , ⇓n
  = n

--
-- This holds "by construction":
--     nf? t ⇓ n → nf t ≡ n
--

nf⇓→nf : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : nf? t ⇓ n) → nf t ≡ n
nf⇓→nf {α} {Γ} t ⇓n
  with all-scv t (id-env Γ) (sce-id-env Γ)
... | u′ , p′ , ⇓u′ , ≈u′
  with reify u′ p′
... | n′ , ⇓n′ , ≈n′
  = ⇓-det (bind⇓ readback ⇓u′ ⇓n′) ⇓n
