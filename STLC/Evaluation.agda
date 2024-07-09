module STLC.Evaluation where

open import Prelude
open import Data.Nat
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas

data _⟶_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    if-true : {t s : Γ ⊢ σ} → if true then t else s ⟶ t
    if-false : {t s : Γ ⊢ σ} → if false then t else s ⟶ s
    ξ-if : {t t' : Γ ⊢ Bool}{s₁ s₂ : Γ ⊢ σ} → t ⟶ t' → if t then s₁ else s₂ ⟶ if t' then s₁ else s₂
    β-ƛ : {t : σ ∷ Γ ⊢ τ}{v : Γ ⊢ σ} → Val v → (ƛ t) · v ⟶ t [ v /x]
    ξ-·₁ : {t t' : Γ ⊢ σ ⇒ τ}{s : Γ ⊢ σ} → t ⟶ t' → t · s ⟶ t' · s
    ξ-·₂ : {v : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → Val v → s ⟶ s' → v · s ⟶ v · s'

infixr 25 _‣_
data _⟶⋆_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    ✦ : {t : Γ ⊢ σ} → t ⟶⋆ t
    _‣_ : {t u v : Γ ⊢ σ} → t ⟶ u → u ⟶⋆ v → t ⟶⋆ v

infixr 30 _▷_
_▷_ : {t u v : Γ ⊢ σ} → t ⟶⋆ u → u ⟶⋆ v → t ⟶⋆ v
✦ ▷ rs = rs
(r ‣ rs) ▷ rs' = r ‣ rs ▷ rs'

infix 30 _⇓
_⇓ : Γ ⊢ σ → Set
_⇓ {Γ} {σ} t = Σ (Γ ⊢ σ) (λ v → Val v × (t ⟶⋆ v))

V¬⟶ : {v t : Γ ⊢ σ} → Val v → v ⟶ t → ⊥
V¬⟶ V-true () 
V¬⟶ V-false ()
V¬⟶ (V-ƛ t) ()

irredVal : {t t' : Γ ⊢ σ} → Val t → t ⟶⋆ t' → t' ≡ t
irredVal V-true ✦ = refl
irredVal V-false ✦ = refl
irredVal (V-ƛ t) ✦ = refl

mapξ : ∀{Γ Δ σ τ} → (f : Γ ⊢ σ → Δ ⊢ τ) → ({t t' : Γ ⊢ σ} → t ⟶ t' → f t ⟶ f t') → {t t' : Γ ⊢ σ} → t ⟶⋆ t' → f t ⟶⋆ f t'
mapξ f ξ ✦ = ✦
mapξ f ξ (r ‣ rs) = ξ r ‣ mapξ f ξ rs

ξ-if⋆ : {t t' : Γ ⊢ Bool}{s₁ s₂ : Γ ⊢ σ} → t ⟶⋆ t' → if t then s₁ else s₂ ⟶⋆ if t' then s₁ else s₂
ξ-if⋆ {s₁ = s₁} {s₂} = mapξ (if_then s₁ else s₂) ξ-if

ξ-·₁⋆ : {t t' : Γ ⊢ σ ⇒ τ}{s : Γ ⊢ σ} → t ⟶⋆ t' → t · s ⟶⋆ t' · s
ξ-·₁⋆ {s = s} = mapξ (_· s) ξ-·₁

ξ-·₂⋆ : {t : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → Val t → s ⟶⋆ s' → t · s ⟶⋆ t · s'
ξ-·₂⋆ {t = t} v = mapξ (t ·_) (ξ-·₂ v)

ξ-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶ t' → rename ρ t ⟶ rename ρ t'
ξ-rename ρ if-true = if-true 
ξ-rename ρ if-false = if-false
ξ-rename ρ (ξ-if r) = ξ-if (ξ-rename ρ r)
ξ-rename ρ {(ƛ t) · s} (β-ƛ v) = transport (λ y → ((ƛ rename (lift ρ) t) · rename ρ s) ⟶ y) (subst-rename≡rename-subst ρ t {s}) (β-ƛ (renameVal ρ v))
ξ-rename ρ (ξ-·₁ r) = ξ-·₁ (ξ-rename ρ r)
ξ-rename ρ (ξ-·₂ v r) = ξ-·₂ (renameVal ρ v) (ξ-rename ρ r)

ξ-rename⋆ : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶⋆ t' → rename ρ t ⟶⋆ rename ρ t'
ξ-rename⋆ ρ = mapξ (rename ρ) (ξ-rename ρ)

data Steps : ℕ → Γ ⊢ σ → Γ ⊢ σ → Set where
    ✦ : ∀{n} → {t : Γ ⊢ σ} → Steps n t t
    _‣_ : ∀{n} → {t u v : Γ ⊢ σ} → t ⟶ u → Steps n u v → Steps (suc n) t v

sucSteps : ∀{n} → {t t' : Γ ⊢ σ} → Steps n t t' → Steps (suc n) t t'
sucSteps ✦ = ✦
sucSteps (r ‣ rs) = r ‣ sucSteps rs

diamond' : {t u u' : Γ ⊢ σ} → t ⟶ u → t ⟶ u' → Σ (Γ ⊢ σ) (λ v → Steps 1 u v × Steps 1 u' v)
diamond' {u = u} if-true if-true = u , ✦ , ✦ 
diamond' {u = u} if-false if-false = u , ✦ , ✦
diamond' {t = if t then s₁ else s₂} (ξ-if t→t') (ξ-if t→t'') with diamond' t→t' t→t''
... | v , ✦ , ✦ = (if v then s₁ else s₂) , ✦ , ✦
... | v , ✦ , (t''→v ‣ ✦) = (if v then s₁ else s₂) , ✦ , (ξ-if t''→v ‣ ✦)
... | v , (t'→v ‣ ✦) , ✦ = (if v then s₁ else s₂) , (ξ-if t'→v ‣ ✦) , ✦
... | v , (t'→v ‣ ✦) , (t''→v ‣ ✦) = (if v then s₁ else s₂) , (ξ-if t'→v ‣ ✦) , (ξ-if t''→v ‣ ✦)
diamond' {t = (ƛ t) · s} (β-ƛ v) (β-ƛ v') with uniqueVal v v'
... | refl = (t [ s /x]) , ✦ , ✦
diamond' {t = (ƛ t) · s} (β-ƛ v) (ξ-·₂ _ r) = ⊥-elim (V¬⟶ v r)
diamond' {t = t · s} (ξ-·₁ t→t') (ξ-·₁ t→t'') with diamond' t→t' t→t''
... | v , ✦ , ✦ = v · s , ✦ , ✦
... | v , ✦ , (t''→v ‣ ✦) = v · s , ✦ , (ξ-·₁ t''→v ‣ ✦)
... | v , (t'→v ‣ ✦) , ✦ = v · s , (ξ-·₁ t'→v ‣ ✦) , ✦
... | v , (t'→v ‣ ✦) , (t''→v ‣ ✦) = v · s , (ξ-·₁ t'→v ‣ ✦) , (ξ-·₁ t''→v ‣ ✦)
diamond' (ξ-·₁ r) (ξ-·₂ v _) = ⊥-elim (V¬⟶ v r)
diamond' (ξ-·₂ v r1) (β-ƛ v') = let (w , rs₁ , rs₂) = diamond' (β-ƛ v') (ξ-·₂ v r1) in (w , rs₂ , rs₁)
diamond' (ξ-·₂ v _) (ξ-·₁ r) = ⊥-elim (V¬⟶ v r)
diamond' {t = t · s} (ξ-·₂ v s→s') (ξ-·₂ v' s→s'') with uniqueVal v v'
...                                               | refl with diamond' s→s' s→s''
...                                                      | w , ✦ , ✦                    = t · w , ✦ , ✦
...                                                      | w , ✦ , (s''→w ‣ ✦)          = t · w , ✦ , (ξ-·₂ v s''→w ‣ ✦)
...                                                      | w , (s'→w ‣ ✦) , ✦           = t · w , (ξ-·₂ v s'→w ‣ ✦) , ✦
...                                                      | w , (s'→w ‣ ✦) , (s''→w ‣ ✦) = t · w , (ξ-·₂ v s'→w ‣ ✦) , (ξ-·₂ v s''→w ‣ ✦)

confluence' : (n m : ℕ) → {t u u' : Γ ⊢ σ} → Steps n t u → Steps m t u' → Σ (Γ ⊢ σ) (λ v → Steps m u v × Steps n u' v)
confluence' _ _ {u' = u'} ✦ rs = u' , rs , ✦
confluence' _ _ {u = u} rs ✦ = u , ✦ , rs
confluence' (suc n) (suc m) (t→u₁ ‣ u₁→*u) (t→u₂ ‣ u₂→*u') with diamond' t→u₁ t→u₂
... | v , ✦ , ✦ = let (w , u→w , u'→w) = confluence' n m u₁→*u u₂→*u' in w , sucSteps u→w , sucSteps u'→w
... | v , ✦ , (u₂→v ‣ ✦) = let (w , u→*w , u'→*w) = confluence' (suc n) m (u₂→v ‣ u₁→*u) u₂→*u' in w , sucSteps u→*w , u'→*w
... | v , (u₁→v ‣ ✦) , ✦ = let (w , u→*w , u'→*w) = confluence' n (suc m) u₁→*u (u₁→v ‣ u₂→*u') in w , u→*w , sucSteps u'→*w
... | v , (u₁→v ‣ ✦) , (u₂→v ‣ ✦) with confluence' n 1 u₁→*u (u₁→v ‣ ✦) | confluence' 1 m (u₂→v ‣ ✦) u₂→*u'
... | v₁ , ✦ , v→*v₁          | v₂ , v→*v₂ , ✦           = let (w , v₁→*w , v₂→*w) = confluence' n m v→*v₁ v→*v₂ in w , sucSteps v₁→*w , sucSteps v₂→*w
... | v₁ , ✦ , v→*v₁          | v₂ , v→*v₂ , (u'→v₂ ‣ ✦) = let (w , v₁→*w , v₂→*w) = confluence' n m v→*v₁ v→*v₂ in w , sucSteps v₁→*w , (u'→v₂ ‣ v₂→*w)
... | v₁ , (u→v₁ ‣ ✦) , v→*v₁ | v₂ , v→*v₂ , ✦           = let (w , v₁→*w , v₂→*w) = confluence' n m v→*v₁ v→*v₂ in w , (u→v₁ ‣ v₁→*w) , sucSteps v₂→*w
... | v₁ , (u→v₁ ‣ ✦) , v→*v₁ | v₂ , v→*v₂ , (u'→v₂ ‣ ✦) = let (w , v₁→*w , v₂→*w) = confluence' n m v→*v₁ v→*v₂ in w , (u→v₁ ‣ v₁→*w) , (u'→v₂ ‣ v₂→*w)

count-steps : {t t' : Γ ⊢ σ} → t ⟶⋆ t' → ℕ
count-steps ✦ = zero
count-steps (_ ‣ rs) = suc (count-steps rs)

steps : {t t' : Γ ⊢ σ}(t→*t' : t ⟶⋆ t') → Steps (count-steps t→*t') t t'
steps ✦ = ✦
steps (r ‣ rs) = r ‣ steps rs

forgetSteps : ∀{n} → {t t' : Γ ⊢ σ} → Steps n t t' → t ⟶⋆ t'
forgetSteps ✦ = ✦
forgetSteps (r ‣ rs) = r ‣ forgetSteps rs

diamond : {t u u' : Γ ⊢ σ} → t ⟶ u → t ⟶ u' → Σ (Γ ⊢ σ) (λ v → (u ⟶⋆ v) × (u' ⟶⋆ v))
diamond rs rs' = let (v , u→*v , u'→*v) = diamond' rs rs' in v , forgetSteps u→*v , forgetSteps u'→*v

confluence : {t u u' : Γ ⊢ σ} → t ⟶⋆ u → t ⟶⋆ u' → Σ (Γ ⊢ σ) (λ v → (u ⟶⋆ v) × (u' ⟶⋆ v))
confluence rs rs' = let (v , u→*v , u'→*v) = confluence' (count-steps rs) (count-steps rs') (steps rs) (steps rs') 
                    in v , forgetSteps u→*v , forgetSteps u'→*v