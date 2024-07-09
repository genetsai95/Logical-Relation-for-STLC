module STLC.Base where

open import Prelude

-- definition of types
infixr 30 _⇒_
data Type : Set where
    Bool : Type
    _⇒_ : Type → Type → Type

-- definition of contexts
Ctx = List Type

variable
    Γ Δ Θ : Ctx
    σ τ φ ψ : Type

-- definition of terms
data _∋_ : Ctx → Type → Set where
    ze : σ ∷ Γ ∋ σ
    su : Γ ∋ σ → τ ∷ Γ ∋ σ

infix 25 _⊢_
infix 30 if_then_else_
infixr 35 _·_
data _⊢_ : Ctx → Type → Set where
    `_ : Γ ∋ σ → Γ ⊢ σ
    true false : Γ ⊢ Bool
    _·_ : Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
    ƛ_ : σ ∷ Γ ⊢ τ → Γ ⊢ σ ⇒ τ
    if_then_else_ : Γ ⊢ Bool → Γ ⊢ σ → Γ ⊢ σ → Γ ⊢ σ

app-term-≡ : {t₁ t₂ : Γ ⊢ σ ⇒ τ}{s₁ s₂ : Γ ⊢ σ} → t₁ ≡ t₂ → s₁ ≡ s₂ → (t₁ · s₁) ≡ (t₂ · s₂)
app-term-≡ refl refl = refl

if-term-≡ : {b₁ b₂ : Γ ⊢ Bool}{t₁ t₂ s₁ s₂ : Γ ⊢ σ} → b₁ ≡ b₂ → t₁ ≡ t₂ → s₁ ≡ s₂ → if b₁ then t₁ else s₁ ≡ if b₂ then t₂ else s₂
if-term-≡ refl refl refl = refl

`-elim-≡ : {x y : Γ ∋ σ} → (` x) ≡ (` y) → x ≡ y
`-elim-≡ refl = refl

-- definition of values
data Val : Γ ⊢ σ → Set where
    V-true : Val {Γ} true
    V-false : Val {Γ} false
    V-ƛ : (t : σ ∷ Γ ⊢ τ) → Val (ƛ t)

uniqueVal : {t : Γ ⊢ σ}(u v : Val t) → u ≡ v
uniqueVal V-true V-true = refl
uniqueVal V-false V-false = refl
uniqueVal (V-ƛ t) (V-ƛ .t) = refl