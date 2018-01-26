module STLC-Delay.StabilityAndCompleteness where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.Conversion
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normalizer
open import STLC-Delay.OPEMoreLemmas
open import STLC-Delay.StrongComputability
open import STLC-Delay.TerminatingNormalizer

--
-- Stability: nf (embNf n) ≡ n .
--

-- ∃ λ u → eval (embNf n) (id-env Γ) ⇓ u × readback u ⇓ n
-- ∃ λ us → eval (embNeNf ns) (id-env Γ) ⇓ ne us × readback* us ⇓ ns

var≤∘suc : ∀ {α γ Β Γ} (η : Β ≤ γ ∷ Γ) (x : Var Γ α) →
  var≤ η (suc x) ≡ var≤ (η ● wk) x
var≤∘suc (≤weak η) x =
  cong suc (var≤∘suc η x)
var≤∘suc (≤lift η) x
  rewrite η ● ≤id ≡ η ∋ η●≤id η
  = refl

eval-embVar≤⇓ : ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  eval (embVar x) (env≤ η id-env) ⇓ ne (var (var≤ η x))
eval-embVar≤⇓ η zero = now⇓
eval-embVar≤⇓ η (suc x)
  rewrite env≤ η (env≤ wk id-env) ≡ env≤ (η ● wk) id-env ∋ env≤∘ η wk id-env |
          var≤ η (suc x) ≡ var≤ (η ● wk) x ∋ var≤∘suc η x
  = eval-embVar≤⇓ (η ● wk) x

eval-embVar⇓ : ∀ {α Γ} (x : Var Γ α) →
  eval (embVar x) id-env ⇓ ne (var x)
eval-embVar⇓ {α} {Γ} x
  with eval-embVar≤⇓ ≤id x
... | r
  rewrite env≤ ≤id id-env ≡ id-env ∋ env≤-≤id {Γ} {Γ} id-env |
          var≤ ≤id x ≡ x ∋ var≤-≤id x
  = r

mutual

  stable⇓ : ∀ {α Γ} (n : Nf Γ α) →
    ∃ λ u → eval (embNf n) id-env ⇓ u × readback u ⇓ n
  stable⇓ {⋆} (ne⋆ ns)
    with stable*⇓ ns
  ... | us , ⇓us , ⇓ns
    = ne us , ⇓us , map⇓ ne⋆ ⇓ns
  stable⇓ {α ⇒ β} {Γ} (lam n)
    with stable⇓ n
  ... | u , ⇓u , ⇓n
    = lam (embNf n) id-env ,
      now⇓ ,
      later⇓ (later⇓ (map⇓ lam (bind⇓ readback ⇓u ⇓n)))

  stable*⇓ : ∀ {α Γ} (ns : NeNf Γ α) →
    ∃ λ us → eval (embNeNf ns) id-env ⇓ ne us × readback* us ⇓ ns
  stable*⇓ (var x) =
    var x , eval-embVar⇓ x , now⇓
  stable*⇓ (app ns n)
    with stable*⇓ ns | stable⇓ n
  ... | us , ⇓us , ⇓ns | u , ⇓u , ⇓n
    = app us u , bind2⇓ apply ⇓us ⇓u now⇓ , map2⇓ app ⇓ns ⇓n

-- nf (embNf n) ≡ n

stable : ∀ {α Γ} (n : Nf Γ α) → nf (embNf n) ≡ n
stable n
  with stable⇓ n
... | u , ⇓u , ⇓n
  = nf⇓→nf (embNf n) (bind⇓ readback ⇓u ⇓n)

--
-- Completeness: terms are convertible to their normal forms.
--

complete : ∀ {α Γ} (t : Tm Γ α) → t ≈ embNf (nf t)

complete t
  with all-scv t id-env sce-id-env
... | u , p , ⇓u , ≈u
  with reify u p
... | n , ⇓n , ≈n
  = begin
  t
    ≈⟨ ≈sym ≈[ı] ⟩
  t [ ı ]
    ≈⟨ ≈cong[] ≈refl (≈≈sym embEnv∘id-env) ⟩
  t [ embEnv id-env ]
    ≈⟨ ≈u ⟩
  embVal u
    ≈⟨ ≈n ⟩
  embNf n
  ∎
  where open ≈-Reasoning
