-- Proving the Strong Normaliaztion of STLC with Logical Predicate
module StrongNormalization where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Evaluation
open import STLC.Lemmas

-- define logical predicate for strong normalization
SN : (σ : Type) → [] ⊢ σ → Set
SN Bool e = e ⇓ 
SN (σ ⇒ τ) e = e ⇓ × ((e' : [] ⊢ σ) → SN σ e' → SN τ (e · e'))

-- This predicate implies strong normalization
lem[SN⇒⇓] : (e : [] ⊢ σ) → SN σ e → e ⇓
lem[SN⇒⇓] {Bool} e p = p 
lem[SN⇒⇓] {σ ⇒ τ} e (p , _) = p

-- terms substitued with values satisfy SN
data SubSN : {Γ : Ctx} → Sub Γ [] → Set where
    [] : SubSN []
    _∷_ : {e : [] ⊢ σ}{ts : Sub Γ []} → SN σ e → SubSN ts → SubSN (e ∷ ts)

syntax SubSN {Γ} γ = γ ⊨ Γ

lookupSubSN : ∀{σ} → {γ : Sub Γ []}(x : Γ ∋ σ) → SubSN γ → SN σ (lookup x γ)
lookupSubSN ze (p ∷ _) = p
lookupSubSN (su x) (_ ∷ ps) = lookupSubSN x ps

lem[SN-backward] : {e e' : [] ⊢ σ} → e ⟶ e' → SN σ e' → SN σ e
lem[SN-backward] {Bool} r (t , v , rs) = t , v , (r ‣ rs)
lem[SN-backward] {σ ⇒ τ} r ((t , v , rs) , f) = (t , v , (r ‣ rs)) , λ e' p' → lem[SN-backward] (ξ-·₁ r) (f e' p')

lem[SN-forward] : {e e' : [] ⊢ σ} → e ⟶ e' → SN σ e → SN σ e'
lem[SN-forward] {Bool} {e' = e'} r (.true , V-true , (r' ‣ rs)) with pr₂ (diamond r r') 
... | e'→*v , u→*v = let (v→*w , true→*w) = pr₂ (confluence u→*v rs) 
                     in true , V-true , transport (λ y → e' ⟶⋆ y) (irredVal V-true true→*w) (e'→*v ▷ v→*w)
lem[SN-forward] {Bool} {e' = e'} r (.false , V-false , (r' ‣ rs)) with pr₂ (diamond r r')
... | e'→*v , u→*v = let (v→*w , false→*w) = pr₂ (confluence u→*v rs) 
                     in false , V-false , transport (λ y → e' ⟶⋆ y) (irredVal V-false false→*w) (e'→*v ▷ v→*w)
lem[SN-forward] {σ ⇒ τ} {e' = e'} r ((t , v , e→*t) , f) with pr₂ (confluence (r ‣ ✦) e→*t)
... | e'→*e'' , t→*e'' = (t , v , transport (λ y → e' ⟶⋆ y) (irredVal v t→*e'') e'→*e'') , 
                         λ e'' p → lem[SN-forward] (ξ-·₁ r) (f e'' p)

lem[SN-backward*] : {e e' : [] ⊢ σ} → e ⟶⋆ e' → SN σ e' → SN σ e
lem[SN-backward*] ✦ p = p
lem[SN-backward*] (r ‣ rs) p = lem[SN-backward] r (lem[SN-backward*] rs p)

lem[SN-forward*] : {e e' : [] ⊢ σ} → e ⟶⋆ e' → SN σ e → SN σ e'
lem[SN-forward*] ✦ p = p
lem[SN-forward*] (r ‣ rs) p = lem[SN-forward*] rs (lem[SN-forward] r p)

thm[subsSN⇒SN] : (e : Γ ⊢ σ){γ : Sub Γ []} → γ ⊨ Γ → SN σ (e [ γ ])
thm[subsSN⇒SN] (` x) ps = lookupSubSN x ps 
thm[subsSN⇒SN] true ps = true , V-true , ✦ 
thm[subsSN⇒SN] false ps = false , V-false , ✦
thm[subsSN⇒SN] {σ = Bool} (if e then e₁ else e₂) ps with thm[subsSN⇒SN] e ps | thm[subsSN⇒SN] e₁ ps | thm[subsSN⇒SN] e₂ ps
... | true  , v , e[γ]→*t | t₁ , v₁ , e₁[γ]→*t₁ | _                   = t₁ , v₁ , ξ-if⋆ e[γ]→*t ▷ (if-true  ‣ e₁[γ]→*t₁)
... | false , v , e[γ]→*t | _                   | t₂ , v₂ , e₂[γ]→*t₂ = t₂ , v₂ , ξ-if⋆ e[γ]→*t ▷ (if-false ‣ e₂[γ]→*t₂)
thm[subsSN⇒SN] {σ = σ ⇒ τ} (if e then e₁ else e₂) ps with thm[subsSN⇒SN] e ps | thm[subsSN⇒SN] e₁ ps | thm[subsSN⇒SN] e₂ ps
... | true  , v , e[γ]→*t | (t₁ , v₁ , e₁[γ]→*t₁) , f | _                         = (t₁ , v₁ , ξ-if⋆ e[γ]→*t ▷ (if-true  ‣ e₁[γ]→*t₁)) , λ e' p' → lem[SN-backward*] (ξ-·₁⋆ (ξ-if⋆ e[γ]→*t ▷ (if-true  ‣ ✦))) (f e' p')
... | false , v , e[γ]→*t | _                         | (t₂ , v₂ , e₂[γ]→*t₂) , f = (t₂ , v₂ , ξ-if⋆ e[γ]→*t ▷ (if-false ‣ e₂[γ]→*t₂)) , λ e' p' → lem[SN-backward*] (ξ-·₁⋆ (ξ-if⋆ e[γ]→*t ▷ (if-false ‣ ✦))) (f e' p')
thm[subsSN⇒SN] (e₁ · e₂) {γ} ps = pr₂ (thm[subsSN⇒SN] e₁ ps) (subst e₂ γ) (thm[subsSN⇒SN] e₂ ps)
thm[subsSN⇒SN] (ƛ_ {σ = σ} {τ = τ} e) {γ} ps = ((ƛ (e [ γ ↑ ])) , V-ƛ (e [ γ ↑ ]) , ✦) , f
    where
        ƛe[γ]·e''→e[e''∷γ] : {e'' : [] ⊢ σ}(v : Val e'') → ((ƛ subst e (γ ↑)) · e'') ⟶⋆ subst e (e'' ∷ γ)
        ƛe[γ]·e''→e[e''∷γ] {e'' = e''} v = β-ƛ v ‣ transport (λ y → (subst e (γ ↑) [ e'' /x]) ⟶⋆ y)
                                                             ((subst e (γ ↑) [ e'' /x]) ≡⟨ lem[sub1] e γ e'' ⟩ subst e (e'' ∷ γ) ∎)
                                                              ✦
        f : (e' : [] ⊢ σ) → SN σ e' → SN τ ((ƛ subst e (γ ↑)) · e')
        f e' p = let (e'' , v , e'→*e'') = lem[SN⇒⇓] e' p 
                 in lem[SN-backward*] (ξ-·₂⋆ (V-ƛ (subst e (γ ↑))) e'→*e'' ▷ ƛe[γ]·e''→e[e''∷γ] v) (thm[subsSN⇒SN] e (lem[SN-forward*] e'→*e'' p ∷ ps))

thm[strong-normalization] : (e : [] ⊢ σ) → e ⇓
thm[strong-normalization] {σ} e = lem[SN⇒⇓] e (transport (SN σ) (subst-idSub e) (thm[subsSN⇒SN] e []))

test : [] ⊢ Bool ⇒ Bool
test = (ƛ (if (` ze) then (ƛ (` ze)) else (ƛ (` ze)))) · false

test-norm = thm[strong-normalization] test

