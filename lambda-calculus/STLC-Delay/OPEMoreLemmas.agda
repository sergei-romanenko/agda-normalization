module STLC-Delay.OPEMoreLemmas where

open import STLC-Delay.Utils
open import STLC-Delay.DelayMonad
open import STLC-Delay.Syntax
open import STLC-Delay.OPE
open import STLC-Delay.OPELemmas
open import STLC-Delay.Normaliser

mutual

  eval≤ : ∀ {α Β Γ Δ i} (η : Β ≤ Γ) (t : Tm Δ α) (ρ : Env Γ Δ) →
    (val≤ η <$> eval t ρ) ~⟨ i ⟩~ eval t (env≤ η ρ)
  eval≤ η ø (u ∷ ρ) = ~now (val≤ η u)
  eval≤ η (f ∙ a) ρ = begin
    (val≤ η <$> (eval f ρ >>= λ u → eval a ρ >>= apply u))
      ≡⟨⟩
    ((eval f ρ >>= (λ u → eval a ρ >>= apply u)) >>= λ v → now (val≤ η v))
      ≈⟨ bind-assoc (eval f ρ) ⟩
    (eval f ρ >>= λ u → (eval a ρ >>= apply u) >>= λ v → now (val≤ η v))
      ≈⟨ bind-cong-r (eval f ρ) (λ u → bind-assoc (eval a ρ)) ⟩
    (eval f ρ >>= λ u → eval a ρ >>= λ v →
      apply u v >>= λ w → now (val≤ η w))
      ≡⟨⟩
    (eval f ρ >>= λ u → eval a ρ >>= λ v → val≤ η <$> apply u v)
      ≈⟨ bind-cong-r (eval f ρ)
                     (λ u → bind-cong-r (eval a ρ) (apply≤ η u)) ⟩
    (eval f ρ >>= λ u → eval a ρ >>= λ v → apply (val≤ η u) (val≤ η v))
      ≡⟨⟩
    (eval f ρ >>= λ u → now (val≤ η u) >>=
      λ u′ → eval a ρ >>= λ v → apply u′ (val≤ η v))
      ≈⟨ ~sym $ bind-assoc (eval f ρ) ⟩
    ((eval f ρ >>= λ u → now (val≤ η u)) >>=
      λ u′ → eval a ρ >>= λ v → apply u′ (val≤ η v))
      ≈⟨ bind-cong-r (eval f ρ >>= λ u → now (val≤ η u))
        (λ u′ → ~sym $ bind-assoc (eval a ρ)) ⟩
    ((eval f ρ >>= λ u → now (val≤ η u)) >>=
      λ u′ → (eval a ρ >>= λ v → now (val≤ η v)) >>= apply u′)
      ≡⟨⟩
    ((val≤ η <$> eval f ρ) >>= λ u′ → (val≤ η <$> eval a ρ) >>= apply u′)
      ≈⟨ bind-cong (eval≤ η f ρ) (λ u′ → bind-cong-l (eval≤ η a ρ) (apply u′)) ⟩
    (eval f (env≤ η ρ) >>= (λ u′ → eval a (env≤ η ρ) >>= apply u′))
    ∎
    where open ~-Reasoning
  eval≤ η (ƛ t) ρ =
    ~now (lam t (env≤ η ρ))
  eval≤ η (t [ σ ]) ρ = begin
    (val≤ η <$> eval (t [ σ ]) ρ)
      ≡⟨⟩
    ((eval* σ ρ >>= eval t) >>= now ∘ val≤ η)
      ≈⟨ bind-assoc (eval* σ ρ) ⟩
    (eval* σ ρ >>= (λ ρ′ → eval t ρ′ >>= now ∘ val≤ η))
      ≡⟨⟩
    (eval* σ ρ >>= (λ ρ′ → val≤ η <$> eval t ρ′))
      ≈⟨ bind-cong-r (eval* σ ρ) (λ ρ′ → eval≤ η t ρ′) ⟩
    (eval* σ ρ >>= λ ρ′ → eval t (env≤ η ρ′))
      ≈⟨ ~sym (bind-assoc (eval* σ ρ)) ⟩
    ((eval* σ ρ >>= now ∘ env≤ η) >>= eval t)
      ≡⟨⟩
    ((env≤ η <$> eval* σ ρ) >>= eval t)
      ≈⟨ bind-cong-l (eval*≤ η σ ρ) (eval t) ⟩
    (eval* σ (env≤ η ρ) >>= eval t)
      ≡⟨⟩
    eval (t [ σ ]) (env≤ η ρ)
    ∎
    where open ~-Reasoning


  eval*≤ : ∀ {Β Γ Δ Δ′ i} (η : Β ≤ Γ) (σ : Sub Δ Δ′) (ρ : Env Γ Δ) →
    (env≤ η <$> eval* σ ρ) ~⟨ i ⟩~ eval* σ (env≤ η ρ)
  eval*≤ η ı ρ = ~refl (now (env≤ η ρ))
  eval*≤ η (σ ○ τ) ρ = begin
    (env≤ η <$> eval* (σ ○ τ) ρ)
      ≡⟨⟩
    ((eval* τ ρ >>= eval* σ) >>= now ∘ env≤ η)
      ≈⟨ bind-assoc (eval* τ ρ) ⟩
    (eval* τ ρ >>= λ ρ′ → (eval* σ ρ′ >>= now ∘ env≤ η))
      ≡⟨⟩
    (eval* τ ρ >>= λ ρ′ → (env≤ η <$> eval* σ ρ′))
      ≈⟨ bind-cong-r (eval* τ ρ) (eval*≤ η σ) ⟩
    (eval* τ ρ >>= λ ρ′ → eval* σ (env≤ η ρ′))
      ≡⟨⟩
    (eval* τ ρ >>= λ ρ′ → now (env≤ η ρ′) >>= eval* σ)
      ≈⟨ ~sym $ bind-assoc (eval* τ ρ) ⟩
    ((eval* τ ρ >>= now ∘ env≤ η) >>= eval* σ)
      ≡⟨⟩
    ((env≤ η <$> eval* τ ρ) >>= eval* σ)
      ≈⟨ bind-cong-l (eval*≤ η τ ρ) (eval* σ) ⟩
    (eval* τ (env≤ η ρ) >>= eval* σ)
      ≡⟨⟩
    eval* (σ ○ τ) (env≤ η ρ)
    ∎
    where open ~-Reasoning
  eval*≤ η (t ∷ σ) ρ = begin
    (env≤ η <$> eval* (t ∷ σ) ρ)
      ≡⟨⟩
    (eval* (t ∷ σ) ρ >>= now ∘ env≤ η)
      ≡⟨⟩
    (eval t ρ >>= (λ u → eval* σ ρ >>= now ∘ (_∷_ u)) >>= now ∘ env≤ η)
      ≈⟨ bind-assoc (eval t ρ) ⟩
    (eval t ρ >>= λ u → (eval* σ ρ >>= (λ ρ′ → now (u ∷ ρ′))) >>= now ∘ env≤ η)
      ≈⟨ bind-cong-r (eval t ρ) (λ u → bind-assoc (eval* σ ρ)) ⟩
    (eval t ρ >>= λ u → eval* σ ρ >>= λ ρ′ → now (u ∷ ρ′) >>= now ∘ env≤ η)
      ≡⟨⟩
    (eval t ρ >>= λ u → eval* σ ρ >>= λ ρ′ → now (env≤ η (u ∷ ρ′)))
      ≡⟨⟩
    (eval t ρ >>= λ u → eval* σ ρ >>= λ ρ′ → now (val≤ η u ∷ env≤ η ρ′))
      ≡⟨⟩
    (eval t ρ >>= λ u →
      (eval* σ ρ >>= λ ρ′ → now (env≤ η ρ′) >>= λ ρ′ → now (val≤ η u ∷ ρ′)))
      ≈⟨ bind-cong-r (eval t ρ) (λ u → ~sym $ bind-assoc (eval* σ ρ)) ⟩
    (eval t ρ >>= λ u →
      (eval* σ ρ >>= now ∘ env≤ η) >>= λ ρ′ → now (val≤ η u ∷ ρ′))
      ≡⟨⟩
    (eval t ρ >>= λ u → now (val≤ η u) >>=
      λ u′ → (eval* σ ρ >>= now ∘ env≤ η) >>= λ ρ′ → now (u′ ∷ ρ′))
      ≈⟨ ~sym $ bind-assoc (eval t ρ) ⟩
    ((eval t ρ >>= now ∘ val≤ η) >>=
      λ u′ → (eval* σ ρ >>= now ∘ env≤ η) >>= λ ρ′ → now (u′ ∷ ρ′))
      ≡⟨⟩
    ((val≤ η <$> eval t ρ) >>=
      λ u → (env≤ η <$> eval* σ ρ) >>= λ ρ′ → now (u ∷ ρ′))
      ≈⟨ bind-cong (eval≤ η t ρ)
                   (λ u → bind-cong-l (eval*≤ η σ ρ) (λ ρ′ → now (u ∷ ρ′))) ⟩
    (eval t (env≤ η ρ) >>=
      λ u → eval* σ (env≤ η ρ) >>= λ ρ′ → now (u ∷ ρ′))
      ≡⟨⟩
    eval* (t ∷ σ) (env≤ η ρ)
    ∎
    where open ~-Reasoning
  eval*≤ η ↑ (u ∷ ρ) = ~refl (now (env≤ η ρ))

  apply≤ : ∀ {α β Β Γ i} (η : Β ≤ Γ)
    (u : Val Γ (α ⇒ β)) (v : Val Γ α) →
    (val≤ η <$> apply u v) ~⟨ i ⟩~ apply (val≤ η u) (val≤ η v)
  apply≤ η (ne us) u =
    ~now (ne (app (neVal≤ η us) (val≤ η u)))
  apply≤ η (lam t ρ) u =
    ~later (beta≤ η t ρ u)

  beta≤ : ∀ {α β Β Γ Δ i} (η : Β ≤ Γ)
    (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) (u : Val Γ α) →
    (val≤ η ∞<$> (beta t ρ u)) ∞~⟨ i ⟩~ beta t (env≤ η ρ) (val≤ η u)
  ~force (beta≤ η t ρ u) = eval≤ η t (u ∷ ρ)


mutual

  readback∘≤ : ∀ {α Β Γ i} (η : Β ≤ Γ) (u : Val Γ α) →
    nf≤ η <$> readback u ~⟨ i ⟩~ readback (val≤ η u)
  readback∘≤ {⋆} η (ne us) = begin
    (nf≤ η <$> readback (ne us))
      ≡⟨⟩
    (nf≤ η <$> (ne⋆ <$> readback* us))
      ≈⟨ map-compose (readback* us) ⟩
    ((nf≤ η ∘ ne⋆) <$> readback* us)
      ≡⟨⟩
    ((ne⋆ ∘ neNf≤ η) <$> readback* us)
      ≈⟨ ~sym $ map-compose (readback* us) ⟩
    (ne⋆ <$> (neNf≤ η <$> readback* us))
      ≈⟨ map-cong ne⋆ (readback*∘≤ η us) ⟩
    (ne⋆ <$> readback* (neVal≤ η us))
      ≡⟨⟩
    readback (val≤ η (ne us))
    ∎
    where open ~-Reasoning
  readback∘≤ {α ⇒ β} η u = ~later (
    begin
      ((eta u ∞>>= λ n → now (lam n)) ∞>>= λ n → now (nf≤ η n))
        ≈⟨ ∞bind-assoc (eta u) ⟩
      (eta u ∞>>= λ n → now (lam n) >>= λ n → now (nf≤ η n))
        ≡⟨⟩
      (eta u ∞>>= λ n → now (nf≤ η (lam n)))
        ≡⟨⟩
      (eta u ∞>>= λ n → now (lam (nf≤ (≤lift η) n)))
        ≡⟨⟩
      (eta u ∞>>= λ n → now (nf≤ (≤lift η) n) >>=
        λ n′ → now (lam n′))
        ≈⟨ ∞~sym $ ∞bind-assoc (eta u) ⟩
      ((eta u ∞>>= λ n → now (nf≤ (≤lift η) n)) ∞>>=
        λ n′ → now (lam n′))
        ≡⟨⟩
      ((nf≤ (≤lift η) ∞<$> eta u) ∞>>= λ n′ → now (lam n′))
        ≈⟨ ∞bind-cong-l (eta≤ η u) (λ n′ → now (lam n′)) ⟩
      (eta (val≤ η u) ∞>>= λ n′ → now (lam n′))
    ∎)
    where open ∞~-Reasoning

  readback*∘≤ : ∀ {α Β Γ i} (η : Β ≤ Γ) (us : NeVal Γ α) →
    neNf≤ η <$> readback* us ~⟨ i ⟩~ readback* (neVal≤ η us)
  readback*∘≤ η (var x) = ~now (var (var≤ η x))
  readback*∘≤ η (app us u) = begin
    (neNf≤ η <$> readback* (app us u))
      ≡⟨⟩
    (readback* us >>= (λ ns → (readback u >>= λ n → now (app ns n))) >>=
      λ nsn → now (neNf≤ η nsn))
      ≈⟨ bind-assoc (readback* us) ⟩
    (readback* us >>= λ ns → (readback u >>= λ n → now (app ns n)) >>=
      λ nsn → now (neNf≤ η nsn))
      ≈⟨ bind-cong-r (readback* us) (λ ns → bind-assoc (readback u)) ⟩
    (readback* us >>= λ ns → readback u >>= λ n → now (app ns n) >>=
      λ nsn → now (neNf≤ η nsn))
      ≡⟨⟩
    (readback* us >>= λ ns →
      readback u >>= λ n → now (app (neNf≤ η ns) (nf≤ η n)))
      ≈⟨ ~sym $ bind-assoc (readback* us) ⟩
    ((readback* us >>= λ ns → now (neNf≤ η ns)) >>=
      λ ns′ → readback u >>= λ n → now (app ns′ (nf≤ η n)))
      ≈⟨ bind-cong-r (readback* us >>= λ ns → now (neNf≤ η ns))
         (λ ns′ → ~sym $ bind-assoc (readback u)) ⟩
    ((readback* us >>= λ ns → now (neNf≤ η ns)) >>=
      λ ns′ → (readback u >>= λ n → now (nf≤ η n)) >>= λ n′ → now (app ns′ n′))
      ≡⟨⟩
    ((neNf≤ η <$> readback* us) >>=
      λ ns′ → (nf≤ η <$> readback u) >>= λ n′ → now (app ns′ n′))
      ≈⟨ bind-cong (readback*∘≤ η us)
         (λ ns′ → bind-cong-l (readback∘≤ η u) (λ n → now (app ns′ n))) ⟩
    (readback* (neVal≤ η us) >>=
      λ ns → readback (val≤ η u) >>= λ n → now (app ns n))
      ≡⟨⟩
    readback* (neVal≤ η (app us u))
    ∎
    where open ~-Reasoning

  eta≤ : ∀{α β Β Γ i} (η : Β ≤ Γ) (u : Val Γ (α ⇒ β)) →
    (nf≤ (≤lift η) ∞<$> eta u) ∞~⟨ i ⟩~ (eta (val≤ η u))
  ~force (eta≤ η u) {j} = begin
    force (nf≤ (≤lift η) ∞<$> eta u)
      ≡⟨⟩
    (apply (val≤ wk u) (ne (var zero)) >>= readback
      >>= (λ n → now (nf≤ (≤lift η) n)))
      ≈⟨ bind-assoc (apply (val≤ wk u) (ne (var zero))) ⟩
    (apply (val≤ wk u) (ne (var zero)) >>= λ v → readback v
      >>= (λ n → now (nf≤ (≤lift η) n)))
      ≡⟨⟩
    (apply (val≤ wk u) (ne (var zero)) >>= λ v →
      nf≤ (≤lift η) <$> readback v)
      ≈⟨ bind-cong-r (apply (val≤ wk u) (ne (var zero)))
         (λ v → readback∘≤ (≤lift η) v) ⟩
    (apply (val≤ wk u) (ne (var zero)) >>= λ v →
      readback (val≤ (≤lift η) v))
      ≡⟨⟩
    (apply (val≤ wk u) (ne (var zero)) >>= λ v →
      now (val≤ (≤lift η) v) >>= readback)
      ≈⟨ ~sym $ bind-assoc (apply (val≤ wk u) (ne (var zero))) ⟩
    ((apply (val≤ wk u) (ne (var zero)) >>= λ v →
      now (val≤ (≤lift η) v)) >>= readback)
      ≡⟨⟩
    ((val≤ (≤lift η) <$> apply (val≤ wk u) (ne (var zero))) >>= readback)
      ≈⟨ bind-cong-l (apply≤ (≤lift η) (val≤ wk u) (ne (var zero)))
        readback ⟩
    ((apply (val≤ (≤lift η) (val≤ wk u)) (val≤ (≤lift η)
      (ne (var zero)))) >>= readback)
      ≡⟨⟩
    (apply (val≤ (≤lift η) (val≤ wk u)) (ne (var zero)) >>= readback)
      ≡⟨ cong (λ w → apply w (ne (var zero)) >>= readback)
              (val≤∘ (≤lift η) wk u) ⟩
    (apply (val≤ (≤lift η ● wk) u) (ne (var zero)) >>= readback)
      ≡⟨⟩
    (apply (val≤ (≤weak (η ● ≤id)) u) (ne (var zero)) >>= readback)
      ≡⟨ cong (λ η′ → apply (val≤ (≤weak η′) u) (ne (var zero)) >>= readback)
              (η●≤id η) ⟩
    (apply (val≤ (≤weak η) u) (ne (var zero)) >>= readback)
      ≡⟨ cong (λ η′ → apply (val≤ (≤weak η′) u) (ne (var zero)) >>= readback)
              (sym $ ≤id●η η) ⟩
    (apply (val≤ (≤weak (≤id ● η)) u) (ne (var zero)) >>= readback)
      ≡⟨⟩
    (apply (val≤ (wk ● η) u) (ne (var zero)) >>= readback)
      ≡⟨ cong (λ u′ → apply u′ (ne (var zero)) >>= readback)
              (sym $ val≤∘ wk η u) ⟩
    (apply (val≤ wk (val≤ η u)) (ne (var zero)) >>= readback)
      ≡⟨⟩
    force (eta (val≤ η u))
    ∎
    where open ~-Reasoning


readback≤⇓ : ∀ {α Β Γ} (η : Β ≤ Γ) (u : Val Γ α)
  {n} (⇓n : readback u ⇓ n) →
  readback (val≤ η u) ⇓ nf≤ η n
readback≤⇓ η u ⇓n =
  subst~⇓ (readback∘≤ η u) (map⇓ (nf≤ η) ⇓n)

readback*≤⇓ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : NeVal Γ α)
  {ns} (⇓ns : readback* us ⇓ ns) →
  readback* (neVal≤ η us) ⇓ neNf≤ η ns
readback*≤⇓ η us ⇓ns =
  subst~⇓ (readback*∘≤ η us) (map⇓ (neNf≤ η) ⇓ns)
