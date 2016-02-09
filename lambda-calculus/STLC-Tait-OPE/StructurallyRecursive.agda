module STLC-Tait-OPE.StructurallyRecursive where

open import STLC-Tait-OPE.Util
open import STLC-Tait-OPE.Syntax
open import STLC-Tait-OPE.StrongComputability

--
-- Structurally recursive evaluator.
--

mutual

  infix 4 ⟦_⟧_&_ ⟦_⟧*_&_
  infixl 5 _⟨∙⟩_&_

  ⟦_⟧_&_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) {w : Val Γ α} →
    ⟦ t ⟧ ρ ⇓ w → ∃ λ w′ → w′ ≡ w

  ⟦ ø ⟧ u ∷ ρ & ø⇓ =
    u , refl
  ⟦ t ∙ t′ ⟧ ρ & ∙⇓ ⇓u ⇓v ⇓w
    with ⟦ t ⟧ ρ & ⇓u | ⟦ t′ ⟧ ρ & ⇓v
  ... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
  ⟦ ƛ t ⟧ ρ & ƛ⇓ =
    lam t ρ , refl
  ⟦ t [ σ ] ⟧ ρ & []⇓ ⇓θ ⇓w
    with ⟦ σ ⟧* ρ & ⇓θ
  ... | θ , refl = ⟦ t ⟧ θ & ⇓w

  ⟦_⟧*_&_ : ∀ {B Γ Δ} (σ : Sub Γ Δ) (ρ : Env B Γ) {θ : Env B Δ} →
    ⟦ σ ⟧* ρ ⇓ θ → ∃ λ φ → φ ≡ θ

  ⟦ ı ⟧* ρ & ι⇓ =
    ρ , refl
  ⟦ σ₁ ○ σ₂ ⟧* ρ & ○⇓ ⇓θ ⇓φ
    with ⟦ σ₂ ⟧* ρ & ⇓θ
  ... | θ , refl =
    ⟦ σ₁ ⟧* θ & ⇓φ
  ⟦ t ∷ σ ⟧* ρ & ∷⇓ ⇓u ⇓θ
    with ⟦ t ⟧ ρ & ⇓u | ⟦ σ ⟧* ρ & ⇓θ
  ... | u , refl | θ , refl =
    u ∷ θ , refl
  ⟦ ↑ ⟧* u ∷ ρ & ↑⇓ =
    ρ , refl

  _⟨∙⟩_&_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) {w : Val Γ β} →
    u ⟨∙⟩ v ⇓ w → ∃ λ w′ → w′ ≡ w

  ne us ⟨∙⟩ u & ne⇓ =
    ne (app us u) , refl
  lam t ρ ⟨∙⟩ u & lam⇓ ⇓w =
    ⟦ t ⟧ (u ∷ ρ) & ⇓w

⟦⟧-III : ⟦ III ⟧ id-env & ∙⇓ ƛ⇓ (∙⇓ ƛ⇓ ƛ⇓ (lam⇓ ø⇓)) (lam⇓ ø⇓) ≡
  lam ø [] , refl
⟦⟧-III = refl

mutual

  infix 4 ⌜_&_⌝ ⌜_&_⌝*

  ⌜_&_⌝ : ∀ {α Γ} (u : Val Γ α) {n} (⇓n : Quote u ⇓ n) →
    ∃ λ n′ → n′ ≡ n
  ⌜_&_⌝ {⋆} (ne us) (⋆⇓ .us ⇓ns)
    with ⌜ us & ⇓ns ⌝*
  ... | ns′ , refl
    = ne ns′ , refl
  ⌜_&_⌝ {α ⇒ β} f (⇒⇓ ⇓u ⇓n)
    with val≤ wk f ⟨∙⟩ ne (var zero) & ⇓u
  ... | u′ , refl
    with ⌜ u′  & ⇓n ⌝
  ... | n′ , refl
    = lam n′ , refl

  ⌜_&_⌝* : ∀ {α Γ} (us : NeVal Γ α) {ns} (⇓ns : Quote* us ⇓ ns) →
    ∃ λ ns′ → ns′ ≡ ns
  ⌜ var x & var⇓ ⌝* =
    var x , refl
  ⌜ app us u & app⇓ ⇓ns ⇓n ⌝*
    with ⌜ us & ⇓ns ⌝* | ⌜ u & ⇓n ⌝
  ... | ns′ , refl | n′ , refl
    = app ns′ n′ , refl

--
-- Normalizer!
--

nf_&_ : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : Nf t ⇓ n) →
  ∃ λ n′ → n′ ≡ n
nf t & nf⇓ ⇓u ⇓n
  with ⟦ t ⟧ id-env & ⇓u
... | u′ , refl
  with ⌜ u′ & ⇓n ⌝
... | n′ , refl
  = n′ , refl

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf t
  with all-scv t id-env sce-id-env
... | u , p , ⇓u , ≈u
  with all-quote u p
... | n , ⇓n , ≈n
  with nf t & nf⇓ ⇓u ⇓n
... | n′ , n′≡n
  = n′

--
-- This holds "by construction":
--     Nf t ⇓ n → nf t ≡ n
--

-- Nf t ⇓ n → nf t ≡ n

nf⇓→nf : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : Nf t ⇓ n) → nf t ≡ n
nf⇓→nf t {n} (nf⇓ {u = u} ⇓u ⇓n)
  with all-scv t id-env sce-id-env
... | u′ , p′ , ⇓u′ , ≈u′
  with all-quote u′ p′
... | n′ , ⇓n′ , ≈n′
  with nf t & nf⇓ ⇓u′ ⇓n′
... | n′′ , n′′≡n′ rewrite n′′≡n′
  = quote⇓-det ⇓n′ ⇓n (⟦⟧⇓-det ⇓u′ ⇓u refl)

--
-- Stability: nf (embNf n) ≡ n .
--

-- Nf embNf n ⇓ n

var≤∘suc : ∀ {α γ Β Γ} (η : Β ≤ γ ∷ Γ) (x : Var Γ α) →
  var≤ η (suc x) ≡ var≤ (η ● wk) x
var≤∘suc (≤weak η) x =
  cong suc (var≤∘suc η x)
var≤∘suc (≤lift η) x
  rewrite η ● ≤id ≡ η ∋ η●≤id η
  = refl

⟦embVar⟧≤⇓ : ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  ⟦ embVar x ⟧ (env≤ η id-env) ⇓ ne (var (var≤ η x))
⟦embVar⟧≤⇓ η zero = ø⇓
⟦embVar⟧≤⇓ η (suc x)
  rewrite env≤ η (env≤ wk id-env) ≡ env≤ (η ● wk) id-env ∋ env≤∘ η wk id-env |
          var≤ η (suc x) ≡ var≤ (η ● wk) x ∋ var≤∘suc η x
  = []⇓ ↑⇓ (⟦embVar⟧≤⇓ (η ● wk) x)

⟦embVar⟧⇓ : ∀ {α Γ} (x : Var Γ α) →
  ⟦ embVar x ⟧ id-env ⇓ ne (var x)
⟦embVar⟧⇓ {α} {Γ} x
  with ⟦embVar⟧≤⇓ ≤id x
... | r
  rewrite env≤ ≤id id-env ≡ id-env ∋ env≤-≤id {Γ} {Γ} id-env |
          var≤ ≤id x ≡ x ∋ var≤-≤id x
  = r

mutual

  stable⇓ : ∀ {α Γ} (n : Nf Γ α) → Nf embNf n ⇓ n
  stable⇓ (ne ns)
    with stable*⇓ ns
  ... | us , ⇓us , ⇓ns
    = nf⇓ ⇓us (⋆⇓ us ⇓ns)
  stable⇓ (lam n)
    with stable⇓ n
  ... | nf⇓ ⇓u ⇓n
    = nf⇓ ƛ⇓ (⇒⇓ (lam⇓ ⇓u) ⇓n)

  stable*⇓ : ∀ {α Γ} (ns : NeNf Γ α) →
    ∃ λ (us : NeVal Γ α) →
      ⟦ embNeNf ns ⟧ id-env ⇓ ne us × Quote* us ⇓ ns
  stable*⇓ (var x) =
    var x , ⟦embVar⟧⇓ x , var⇓
  stable*⇓ (app ns n) with stable*⇓ ns | stable⇓ n
  ... | us , ⇓us , ⇓ns | nf⇓ {u = u} ⇓u ⇓n =
    app us u , ∙⇓ ⇓us ⇓u ne⇓ , app⇓ ⇓ns ⇓n


-- nf (embNf n) ≡ n

stable : ∀ {α Γ} (n : Nf Γ α) → nf (embNf n) ≡ n
stable n =
  nf⇓→nf (embNf n) (stable⇓ n)


--
-- Completeness: terms are convertible to their normal forms.
--

complete : ∀ {α Γ} (t : Tm Γ α) → t ≈ embNf (nf t)

complete t
  with all-scv t id-env sce-id-env
... | u , p , ⇓u , ≈u
  with all-quote u p
... | n , ⇓n , ≈n
  with nf t & nf⇓ ⇓u ⇓n
... | n′ , n′≡n rewrite n′≡n
  = begin
  t
    ≈⟨ ≈sym ≈id ⟩
  t [ ı ]
    ≈⟨ ≈cong[] ≈refl (≈≈sym embEnv∘id-env) ⟩
  t [ embEnv id-env ]
    ≈⟨ ≈u ⟩
  embVal u
    ≈⟨ ≈n ⟩
  embNf n
  ∎
  where open ≈-Reasoning
