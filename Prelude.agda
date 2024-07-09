module Prelude where

open import Data.Char
open import Agda.Primitive

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

⊥-elim : ∀{ℓ}{A : Set ℓ} → ⊥ → A
⊥-elim ()

Sym : Set
Sym = Char

record Σ (A : Set)(B : A → Set) : Set where
    constructor _,_
    field
        pr₁ : A
        pr₂ : B pr₁
open Σ public
infixr 30 _,_

∃-syntax = Σ
syntax ∃-syntax A (λ x → B) = ∃[ x ∶ A ] B

infixr 25 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

⟨_,_⟩ : {A₁ A₂ B₁ B₂ : Set} → (A₁ → B₁) → (A₂ → B₂) → A₁ × A₂ → B₁ × B₂
⟨ f , g ⟩ (a₁ , a₂) = f a₁ , g a₂

data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

data _≡_ {ℓ}{X : Set ℓ}(x : X) : X → Set ℓ where
    refl : x ≡ x

-- data _≡_ {X : Set}(x : X) : {Y : Set} → Y → Set where
--     refl : x ≡ x

_≡⟨_⟩_ : {X : Set}(x : X){y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ eq = eq

_∎ : {X : Set}(x : X) → x ≡ x
_ ∎ = refl

infix 25 _∎
infixr 20 _≡⟨_⟩_

pair-≡ : {X Y : Set}{x₁ x₂ : X}{y₁ y₂ : Y} → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
pair-≡ refl refl = refl

cong : {X Y : Set}{x₁ x₂ : X}(f : X → Y) → x₁ ≡ x₂ → f x₁ ≡ f x₂
cong f refl = refl

same-arg : {X : Set}{Y : X → Set}(x : X){f g : (a : X) → Y a} → f ≡ g → f x ≡ g x
same-arg x = cong (λ f → f x)

≡-sym : {X : Set}{x y : X} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {X : Set}{x y z : X} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl eq = eq

app-≡ : {X Y : Set}{x₁ x₂ : X}{f g : X → Y} → f ≡ g → x₁ ≡ x₂ → f x₁ ≡ g x₂
app-≡ refl refl = refl

app-≡' : {X Y : Set}{x₁ x₂ : X}{f g : X → Y} → x₁ ≡ x₂ → f ≡ g → f x₁ ≡ g x₂
app-≡' refl refl = refl

transport : {A : Set}(B : A → Set){x y : A} → x ≡ y → B x → B y
transport _ refl bx = bx

_≢_ : {X : Set}(x y : X) → Set
x ≢ y = (x ≡ y) → ⊥

data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

infixr 30 _∷_

infix 22 _∘_
_∘_ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} → ({a : A}(b : B a) → C a b) → (g : (a : A) → B a) → (a : A) → C a (g a)
(f ∘ g) x = f (g x)

id : {X : Set} → X → X
id x = x

-- Decidability
data Dec (A : Set) : Set where
    yes : A → Dec A
    no : ¬ A → Dec A

-- postulate
--     fx : {X : Set}{Y : X → Set}{f g : (x : X) → Y x} → ((x : X) → f x ≡ g x) → f ≡ g

-- _=f=_ : {A : Set}{B : A → Set} → ((a : A) → B a) → ((a : A) → B a) → Set
-- _=f=_ {A = A} f g = (x : A) → f x ≡ g x

-- fsym : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f =f= g → g =f= f
-- fsym eq x = ≡-sym (eq x)

-- ftrans : {A : Set}{B : A → Set}{f g h : (a : A) → B a} → f =f= g → g =f= h → f =f= h
-- ftrans eq1 eq2 x = ≡-trans (eq1 x) (eq2 x)
