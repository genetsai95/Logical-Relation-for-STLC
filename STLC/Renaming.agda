module STLC.Renaming where

open import Prelude
open import STLC.Base

-- renamings
_⊆_ : Ctx → Ctx → Set
Γ ⊆ Δ = ∀{σ} → Γ ∋ σ → Δ ∋ σ

data Ren : Ctx → Ctx → Set where
    [] : Ren [] Δ
    _∷_ : Δ ∋ σ → Ren Γ Δ → Ren (σ ∷ Γ) Δ

lookupRen : Γ ∋ σ → Ren Γ Δ → Δ ∋ σ
lookupRen ze (r ∷ rs) = r
lookupRen (su x) (r ∷ rs) = lookupRen x rs

mapRen : (∀{σ} → Δ ∋ σ → Θ ∋ σ) → Ren Γ Δ → Ren Γ Θ
mapRen f [] = []
mapRen f (r ∷ rs) = f r ∷ mapRen f rs

concatRen : Ren Γ Δ → Ren Δ Θ → Ren Γ Θ
concatRen ρ ρ' = mapRen (λ x → lookupRen x ρ') ρ

lift : Ren Γ Δ → Ren (σ ∷ Γ) (σ ∷ Δ)
lift rs = ze ∷ mapRen su rs

idRen : Ren Γ Γ
idRen {[]} = []
idRen {σ ∷ Γ} = lift idRen

rename : Ren Γ Δ → Γ ⊢ σ → Δ ⊢ σ
rename rs (` x) = ` lookupRen x rs
rename rs true = true
rename rs false = false
rename rs (t · s) = rename rs t · rename rs s
rename rs (ƛ t) = ƛ rename (lift rs) t
rename rs (if b then t₁ else t₂) = if rename rs b then rename rs t₁ else rename rs t₂


-- weakening
wk : Ren Γ (σ ∷ Γ)
wk = mapRen su idRen

weaken : Γ ⊢ σ → τ ∷ Γ ⊢ σ
weaken = rename wk 

-- equalities about renamings
∷-ren-eq : {x y : Δ ∋ σ}{xs ys : Ren Γ Δ} → x ≡ y → xs ≡ ys → _≡_ {X = Ren (σ ∷ Γ) Δ} (x ∷ xs) (y ∷ ys)
∷-ren-eq refl refl = refl

ren-head-eq-elim : {x : Δ ∋ σ}{xs ys : Ren Γ Δ} → _≡_ {X = Ren (σ ∷ Γ) Δ} (x ∷ xs) (x ∷ ys) → xs ≡ ys
ren-head-eq-elim refl = refl

lookupRen-map : (f : ∀{τ} → Δ ∋ τ → Θ ∋ τ){rs : Ren Γ Δ}(x : Γ ∋ σ){t : Δ ∋ σ} → lookupRen x rs ≡ t → lookupRen x (mapRen f rs) ≡ f t
lookupRen-map f {_ ∷ _} ze refl = refl
lookupRen-map f {_ ∷ rs} (su x) refl = lookupRen-map f {rs} x refl

lookupRen-idRen : (x : Γ ∋ σ) → lookupRen x idRen ≡ x
lookupRen-idRen ze = refl
lookupRen-idRen (su x) = lookupRen-map su x (lookupRen-idRen x)

rename-idRen : (t : Γ ⊢ σ) → rename idRen t ≡ t
rename-idRen (` x) = cong `_ (lookupRen-idRen x)
rename-idRen true = refl
rename-idRen false = refl
rename-idRen (t · s) = app-term-≡ (rename-idRen t) (rename-idRen s)
rename-idRen (ƛ t) = cong ƛ_ (rename-idRen t)
rename-idRen (if t then t₁ else t₂) = if-term-≡ (rename-idRen t) (rename-idRen t₁) (rename-idRen t₂)


lookupRen-wk : ∀{τ} → (x : Γ ∋ σ) → lookupRen x (wk {Γ} {τ}) ≡ su x
lookupRen-wk ze = refl
lookupRen-wk (su x) = lookupRen-map su x (lookupRen-wk x)

wk≡su : ∀{τ} → (x : Γ ∋ σ) → lookupRen x (wk {Γ} {τ}) ≡ su x
wk≡su ze = refl
wk≡su (su x) = lookupRen-map su x (wk≡su x)

weaken`≡`su : ∀{τ} → (x : Γ ∋ σ) → weaken {τ = τ} (` x) ≡ (` su x) 
weaken`≡`su x = cong `_ (wk≡su x)

concatRen-lift : ∀{σ} → (ρ : Ren Γ Δ)(ρ' : Ren Δ Θ) → concatRen (lift {σ = σ} ρ) (lift ρ') ≡ lift (concatRen ρ ρ')
concatRen-lift [] ρ' = refl 
concatRen-lift (r ∷ ρ) ρ' = cong (ze ∷_) (∷-ren-eq (lookupRen-map su r refl) (ren-head-eq-elim (concatRen-lift ρ ρ')))

renameVal : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Val t → Val (rename ρ t)
renameVal ρ V-true = V-true 
renameVal ρ V-false = V-false
renameVal ρ (V-ƛ t) = V-ƛ (rename (lift ρ) t)