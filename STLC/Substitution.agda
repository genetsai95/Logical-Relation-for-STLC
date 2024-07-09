module STLC.Substitution where

open import Prelude
open import STLC.Base
open import STLC.Renaming

-- definitions about substitution
data Sub : Ctx → Ctx → Set where
    [] : Sub [] Δ
    _∷_ : Δ ⊢ σ → Sub Γ Δ → Sub (σ ∷ Γ) Δ

mapSub : (∀{σ} → Δ ⊢ σ → Θ ⊢ σ) → Sub Γ Δ → Sub Γ Θ
mapSub _ [] = []
mapSub f (t ∷ ts) = f t ∷ mapSub f ts

lookup : Γ ∋ σ → Sub Γ Δ → Δ ⊢ σ
lookup ze (t ∷ _) = t
lookup (su n) (_ ∷ ts) = lookup n ts

_↑ : Sub Γ Δ → Sub (σ ∷ Γ) (σ ∷ Δ)
ts ↑ = (` ze) ∷ mapSub weaken ts

subst : Γ ⊢ σ → Sub Γ Δ → Δ ⊢ σ
subst (` x) ts = lookup x ts
subst true ts = true
subst false ts = false
subst (t · s) ts = subst t ts · subst s ts
subst (ƛ t) ts = ƛ subst t (ts ↑)
subst (if t then t₁ else t₂) ts = if subst t ts then subst t₁ ts else subst t₂ ts

syntax subst t ts = t [ ts ]

_⊙_ : Sub Γ Δ → Sub Δ Θ → Sub Γ Θ
ts ⊙ ss = mapSub (λ t → subst t ss) ts

idSub : ∀{Γ} → Sub Γ Γ
idSub {[]} = []
idSub {t ∷ Γ} = idSub ↑

_[_/x] : σ ∷ Γ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
t [ s /x] = subst t (s ∷ idSub)

infix 30 _[_/x]


-- equalities about substitution

∷-sub-eq : {Γ Δ : Ctx}{σ : Type} → {t s : Δ ⊢ σ}{ts ss : Sub Γ Δ} → t ≡ s → ts ≡ ss → _≡_ {X = Sub (σ ∷ Γ) Δ}(t ∷ ts) (s ∷ ss)
∷-sub-eq refl refl = refl

sub-head-eq-elim : ∀{σ} → {ts ss : Sub Γ Δ}{t : Δ ⊢ σ} → _≡_ {X = Sub (σ ∷ Γ) Δ} (t ∷ ts) (t ∷ ss) → ts ≡ ss
sub-head-eq-elim refl = refl

mapSub-fusion : ∀{Γ Δ Δ' Δ''} → (f : ∀{σ} → Δ' ⊢ σ → Δ'' ⊢ σ)(g : ∀{σ} → Δ ⊢ σ → Δ' ⊢ σ){ts : Sub Γ Δ} → (mapSub {Γ = Γ} f ∘ mapSub g) ts ≡ mapSub (f ∘ g) ts
mapSub-fusion f g {[]} = refl
mapSub-fusion f g {t ∷ ts} = mapSub f (mapSub g (t ∷ ts))
                           ≡⟨ refl ⟩ mapSub f (g t ∷ mapSub g ts)
                           ≡⟨ refl ⟩ f (g t) ∷ mapSub f (mapSub g ts)
                           ≡⟨ cong (f (g t) ∷_) (mapSub-fusion f g {ts}) ⟩ f (g t) ∷ mapSub (f ∘ g) ts
                           ≡⟨ refl ⟩ (f ∘ g) t ∷ mapSub (f ∘ g) ts
                           ≡⟨ refl ⟩ mapSub (f ∘ g) (t ∷ ts) ∎

mapSub-eq : {f g : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → (t : Δ ⊢ σ) → f t ≡ g t) → (ts : Sub Γ Δ) → mapSub f ts ≡ mapSub g ts
mapSub-eq eqf [] = refl
mapSub-eq eqf (t ∷ ts) = ∷-sub-eq (eqf t) (mapSub-eq eqf ts)

eqSub : (ts ss : Sub Γ Δ) → (∀{σ} → (n : Γ ∋ σ) → lookup n ts ≡ lookup n ss) → ts ≡ ss
eqSub [] [] _ = refl
eqSub (t ∷ ts) (s ∷ ss) eq with eq ze
... | refl = cong (t ∷_) (eqSub ts ss λ n → eq (su n))

lookup-map : (f : ∀{τ} → Δ ⊢ τ → Θ ⊢ τ){ts : Sub Γ Δ}(x : Γ ∋ σ){t : Δ ⊢ σ} → lookup x ts ≡ t → lookup x (mapSub f ts) ≡ f t
lookup-map f {ts = t ∷ ts} ze refl = refl
lookup-map f {ts = t ∷ ts} (su x) refl = lookup-map f {ts = ts} x refl

lookup-idSub : (x : Γ ∋ σ) → lookup x idSub ≡ (` x)
lookup-idSub ze = refl
lookup-idSub {Γ = σ ∷ Γ} (su x) = 
                                    lookup x (mapSub weaken idSub)
                                ≡⟨ lookup-map weaken {ts = idSub} x (lookup-idSub x) ⟩ 
                                    weaken (` x)
                                ≡⟨ weaken`≡`su x ⟩
                                    (` su x)
                                ∎

lookup-su : ∀{τ τ'} → (x : Γ ∋ σ)(t : Δ ⊢ τ)(s : Δ ⊢ τ')(ts : Sub Γ Δ) → lookup (su x) (t ∷ ts) ≡ lookup (su x) (s ∷ ts)
lookup-su x t s ts = refl

subst-idSub : (t : Γ ⊢ σ) → subst t idSub ≡ t
subst-idSub (` x) = lookup-idSub x
subst-idSub true = refl
subst-idSub false = refl
subst-idSub (t · s) = app-term-≡ (subst-idSub t) (subst-idSub s)
subst-idSub (ƛ t) = cong ƛ_ (subst-idSub t)
subst-idSub (if b then t₁ else t₂) = if-term-≡ (subst-idSub b) (subst-idSub t₁) (subst-idSub t₂)

lookup-⊙ : ∀{σ} → {ts : Sub Γ Δ}{ss : Sub Δ Θ}(x : Γ ∋ σ) → lookup x (ts ⊙ ss) ≡ subst (lookup x ts) ss
lookup-⊙ {ss = ss} x = lookup-map (λ t → subst t ss) x refl

mapSub-id : (ts : Sub Γ Δ) → mapSub id ts ≡ ts
mapSub-id [] = refl
mapSub-id (t ∷ ts) = cong (t ∷_) (mapSub-id ts)

_⊙idSub : (ts : Sub Γ Δ) → (ts ⊙ idSub) ≡ ts
ts ⊙idSub = mapSub (λ t → subst t idSub) ts
          ≡⟨ mapSub-eq subst-idSub ts ⟩ 
            mapSub id ts
          ≡⟨ mapSub-id ts ⟩
            ts
          ∎

idSub⊙ : (ts : Sub Γ Δ) → (idSub ⊙ ts) ≡ ts
idSub⊙ ts = eqSub (idSub ⊙ ts) ts eq-each
  where
    eq-each : ∀{Γ Δ σ} → {ts : Sub Γ Δ}(x : Γ ∋ σ) → lookup x (idSub ⊙ ts) ≡ lookup x ts
    eq-each ze = refl 
    eq-each {ts = ts} (su x) = lookup x (mapSub (λ t → subst t ts) (mapSub weaken idSub))
                             ≡⟨ lookup-map (λ t → subst t ts) x refl ⟩ 
                               subst (lookup x (mapSub weaken idSub)) ts
                             ≡⟨ cong (λ y → subst y ts) (lookup-map weaken x refl) ⟩ 
                               subst (weaken (lookup x idSub)) ts
                             ≡⟨ cong (λ y → subst (weaken y) ts) (lookup-idSub x) ⟩ 
                               lookup (lookupRen x wk) ts
                             ≡⟨ cong (λ y → lookup y ts) (lookupRen-wk x) ⟩
                               lookup (su x) ts
                             ∎