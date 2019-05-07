module STLC where
open import Relation.Nullary
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality using (cong₂;cong)
open import Data.List
open import Data.Unit

data Type : Set where
  unit  : Type
  _→'_  : Type → Type → Type

Ctx : Set
Ctx = List Type

data _∈_ : Type → Ctx → Set where
  hd : ∀ {t₀ Γ} → t₀ ∈ (t₀ ∷ Γ)
  tl : ∀ {t₀ t₁ Γ} → t₀ ∈ Γ → t₀ ∈ (t₁ ∷ Γ)

data Exp (Γ : Ctx) : Type → Set where
  <>'   :                Exp Γ unit
  Var   : ∀ {t}        → t ∈ Γ → Exp Γ t
  λ'    : ∀ {t₀ t₁}    → Exp (t₀ ∷ Γ) t₁ → Exp Γ (t₀ →' t₁)
  _∙_   : ∀ {t₀ t₁}    → Exp Γ (t₀ →' t₁) → Exp Γ t₀ → Exp Γ t₁

evalT : Type → Set
evalT unit = ⊤
evalT (t →' t₁) = evalT t → evalT t₁

env : Ctx → Set
env Γ = ∀ t → t ∈ Γ → evalT t

extend' : ∀ Δ {Γ} → env (Δ ++ Γ) → (t : Type) → evalT t → env (Δ ++ t ∷ Γ)
extend' [] ρ t x _ hd = x
extend' [] ρ t x _ (tl i) = ρ _ i
extend' (x₁ ∷ Δ) ρ t x _ hd = ρ x₁ hd
extend' (x₁ ∷ Δ) ρ t x _ (tl i) = extend' Δ (λ t₁ x₂ → ρ t₁ (tl x₂)) t x _ i

extend : ∀{Γ} → env Γ → (t : Type) → evalT t → env (t ∷ Γ)
extend = extend' []

eval : forall {Γ τ} -> env Γ →  Exp Γ τ -> evalT τ
eval ρ <>' = tt
eval ρ (Var x) = ρ _ x
eval ρ (λ' x) = λ x₁ → eval (extend ρ _ x₁) x
eval ρ (x ∙ x₁) = eval ρ x (eval ρ x₁)

wkVar : ∀ Δ {Γ t₀ t₁} -> t₀ ∈ (Δ ++ Γ) -> t₀ ∈ (Δ ++ t₁ ∷ Γ)
wkVar [] x = tl x
wkVar (x₁ ∷ Δ) hd = hd
wkVar (x₁ ∷ Δ) (tl x) = tl (wkVar Δ x)

weaken' : ∀ Δ {Γ t₀ t₁} → Exp (Δ ++ Γ) t₀ → Exp (Δ ++ t₁ ∷ Γ) t₀
weaken' Δ <>' = <>'
weaken' Δ (Var x) = Var (wkVar Δ x)
weaken' Δ (λ' t) = λ' (weaken' (_ ∷ Δ) t)
weaken' Δ (t ∙ t₁) = weaken' Δ t ∙ weaken' Δ t₁

weaken : ∀ {Γ t₀ t₁} → Exp Γ t₀ → Exp (t₁ ∷ Γ) t₀
weaken = weaken' []

Subst : Ctx -> Ctx -> Set
Subst Δ Γ = ∀ {A} -> A ∈ Δ → Exp Γ A

cons : ∀ {Δ Γ} A -> Subst Δ Γ -> Subst (A ∷ Δ) (A ∷ Γ)
cons _ σ hd = Var hd
cons _ σ (tl i) = weaken (σ i)


substT : ∀ {Δ Γ A} -> Subst Δ Γ -> Exp Δ A → Exp Γ A
substT σ <>' = <>'
substT σ (Var x) = σ x
substT σ (λ' {ty} e) = λ' (substT (cons ty σ) e)
substT σ (e ∙ e₁) = substT σ e ∙ substT σ e₁

evalS : ∀ {Γ Δ} -> env Δ → Subst Γ Δ -> env Γ
evalS ρ σ _ i = eval ρ (σ i)

postulate
  depExt : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ z -> f z ≡ g z) -> f ≡ g

ext : ∀ {A B : Set} {f g : A -> B} -> (∀ z -> f z ≡ g z) -> f ≡ g
ext = depExt

lemmaExch : ∀ Γ {Δ} (ρ : env (Γ ++ Δ)) (ty : Type) (z : evalT ty) t0 z₁ t i
   -> extend (extend' Γ ρ ty z) t0 z₁ t i ≡ extend' (t0 ∷ Γ) (extend ρ t0 z₁) ty z t i
lemmaExch Γ ρ ty z t0 z₁ .t0 hd = refl
lemmaExch [] ρ ty z t0 z₁ t1 (tl i) = refl
lemmaExch (x ∷ Γ) ρ ty z t0 z₁ t1 (tl i) = refl

lemmaExch' : ∀ Γ {Δ} (ρ : env (Γ ++ Δ)) (ty : Type) (z : evalT ty) t0 z₁
   -> extend (extend' Γ ρ ty z) t0 z₁ ≡ extend' (t0 ∷ Γ) (extend ρ t0 z₁) ty z
lemmaExch' Γ ρ ty z t0 z₁ = depExt λ z₂ → depExt (lemmaExch Γ ρ ty z t0 z₁ z₂)

congEnv : ∀ {Γ T} {ρ1 ρ2 : env Γ} (t : Exp Γ T)  -> ρ1 ≡ ρ2 -> eval ρ1 t ≡ eval ρ2 t
congEnv  t refl = refl

extend-var : ∀ Γ {Δ} (ρ : env (Γ ++ Δ)) (ty : Type) (z : evalT ty) Z x
  -> extend' Γ ρ ty z Z (wkVar Γ x) ≡ ρ Z x
extend-var [] ρ ty z Z x = refl
extend-var (x₁ ∷ Γ) ρ ty z .x₁ hd = refl
extend-var (x₁ ∷ Γ) ρ ty z Z (tl x) = extend-var Γ (λ t z₁ → ρ t (tl z₁)) ty z Z x

-- | A weakened term in a corresponding environment is equivalent under eval
eval-wk' : ∀ {Γ Δ} (ρ : env (Γ ++ Δ)) (ty : Type) (z : evalT ty) {Z} (t : Exp (Γ ++ Δ) Z)
  -> eval (extend' Γ ρ ty z) (weaken' Γ t) ≡ eval ρ t
eval-wk' ρ ty z <>' = refl
eval-wk' {Γ} ρ ty z (Var x) = extend-var Γ ρ ty z _ x
eval-wk' {Γ} ρ ty z (λ'  {t0} t) = depExt λ z₁ →  trans (congEnv (weaken' (t0 ∷ Γ) t) (lemmaExch' Γ ρ ty z t0 z₁))
                                                         (eval-wk' {t0 ∷ Γ}  (extend ρ t0 z₁) ty z t)
eval-wk' {Γ} ρ ty z (t ∙ t₁) = cong₂ (λ f x → f x) (eval-wk' {Γ} ρ ty z t) (eval-wk' {Γ} ρ ty z t₁)

eval-wk : ∀ {Δ} (ρ : env Δ) (ty : Type) (z : evalT ty) {Z} (t : Exp Δ Z) -> eval (extend ρ ty z) (weaken t) ≡ eval ρ t
eval-wk = eval-wk'

esl : ∀ {Δ Γ} (ρ : env Δ) (σ : Subst Γ Δ) (ty : Type) (z : evalT ty) {Z} (i : Z ∈ (ty ∷ Γ))
   -> evalS (extend ρ ty z) (cons ty σ) _ i ≡ extend (evalS ρ σ) ty z _ i
esl ρ σ ty z hd = refl
esl ρ σ ty z (tl i) = eval-wk ρ ty z (σ i)

esl' : ∀ {Δ Γ} (ρ : env Δ) (σ : Subst Γ Δ) (ty : Type) (z : evalT ty)
   -> evalS (extend ρ ty z) (cons ty σ)  ≡ extend (evalS ρ σ) ty z
esl' ρ σ ty z = depExt λ ty1 → depExt λ z₁ → esl ρ σ ty z z₁

lemma : ∀ {Δ Γ T} (ρ : env Δ) (σ : Subst Γ Δ) ty z (t : Exp (ty ∷ Γ) T)
  -> eval (evalS (extend ρ ty z) (cons ty σ)) t ≡ eval (extend (evalS ρ σ) ty z) t
lemma ρ σ ty z t = congEnv t (esl' ρ σ ty z)

-- Substitution lemma
sl : ∀ {Δ Γ T} (ρ : env Δ) (σ : Subst Γ Δ) (t : Exp Γ T)
  -> eval ρ (substT σ t) ≡ eval (evalS ρ σ) t
sl ρ σ <>' = refl
sl ρ σ (Var x) = refl
sl ρ σ (λ' {ty} t) = ext λ z → trans (sl (extend ρ ty z) (cons ty σ) t) (lemma ρ σ ty z t)
sl ρ σ (t ∙ t₁) = cong₂ (λ f x → f x) (sl ρ σ t) (sl ρ σ t₁)
