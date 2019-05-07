open import Relation.Nullary
open import Agda.Builtin.Equality
open import Data.List

-- Assume a lattice
postulate L : Set
postulate _⊑_ : L → L → Set

{- Representation of DCC types and terms -}
data Type : Set where
  unit  : Type
  _→'_  : Type → Type → Type
  _×'_  : Type → Type → Type
  _+'_  : Type → Type → Type
  T'    : L → Type → Type

data _≼_ : L → Type → Set where
  PFlow     : ∀ {t ℓ ℓ'} → ℓ ⊑ ℓ' → ℓ ≼ (T' ℓ' t)
  PInner    : ∀ {t ℓ ℓ'} → ℓ ≼ t → ℓ ≼ (T' ℓ' t)
  PProduct  : ∀ {t s ℓ } → ℓ ≼ t → ℓ ≼ s → ℓ ≼ (s ×' t)
  PFunction : ∀ {t s ℓ } → ℓ ≼ t → ℓ ≼ (s →' t)

Ctx : Set
Ctx = List Type

data _∈_ : Type → Ctx → Set where
  hd : ∀ {t₀ Γ} → t₀ ∈ (t₀ ∷ Γ)
  tl : ∀ {t₀ t₁ Γ} → t₀ ∈ Γ → t₀ ∈ (t₁ ∷ Γ)

data Exp (Γ : Ctx) : Type → Set where
  Var   : ∀ {t}        → t ∈ Γ → Exp Γ t
  λ'    : ∀ {t₀ t₁}    → Exp (t₀ ∷ Γ) t₁ → Exp Γ (t₀ →' t₁)
  _∙_   : ∀ {t₀ t₁}    → Exp Γ (t₀ →' t₁) → Exp Γ t₀ → Exp Γ t₁
  pair  : ∀ {t₀ t₁}    → Exp Γ t₀ → Exp Γ t₁ → Exp Γ (t₀ ×' t₁)
  π₀    : ∀ {t₀ t₁}    → Exp Γ (t₀ ×' t₁) → Exp Γ t₀
  π₁    : ∀ {t₀ t₁}    → Exp Γ (t₀ ×' t₁) → Exp Γ t₁
  ι₀    : ∀ {t₀ t₁}    → Exp Γ t₀ → Exp Γ (t₀ +' t₁)
  ι₁    : ∀ {t₀ t₁}    → Exp Γ t₁ → Exp Γ (t₀ +' t₁)
  case  : ∀ {t₀ t₁ t₂} → Exp Γ (t₀ +' t₁) → Exp Γ (t₀ →' t₂) → Exp Γ (t₁ →' t₂) → Exp Γ t₂
  η'    : ∀ {t ℓ}      → Exp Γ t → Exp Γ (T' ℓ t)
  bind' : ∀ {t₀ t₁ ℓ}  → ℓ ≼ t₁ → Exp Γ (T' ℓ t₀) → Exp Γ (t₀ →' t₁) → Exp Γ t₁
  <>'   :                Exp Γ unit

-- Permutations and helpers
Superset : Ctx → Ctx → Set
Superset Γ' Γ = ∀ {x} → x ∈ Γ → x ∈ Γ'

Super-cons : ∀{Γ Γ' t} → Superset Γ' Γ → Superset (t ∷ Γ') (t ∷ Γ)
Super-cons x hd = hd
Super-cons x (tl x₁) = tl (x x₁)

Super-++ : ∀{Γ Γ'} → Superset (Γ' ++ Γ) Γ
Super-++ {Γ' = []} x₁ = x₁
Super-++ {Γ' = x ∷ Γ'} x₁ = tl (Super-++ x₁)

-- Typing stuff
weaken : ∀{Γ Γ' t₂} → Superset Γ' Γ → Exp Γ t₂ → Exp Γ' t₂
weaken x <>' = <>'
weaken {t₂ = t₂} x (Var x₁) = Var (x x₁)
weaken x (λ' {t₀} x₁) = λ' (weaken (Super-cons x) x₁)
weaken x (x₁ ∙ x₂) = (weaken x x₁) ∙ (weaken x x₂)
weaken x (pair x₁ x₂) = pair (weaken x x₁) (weaken x x₂)
weaken x (π₀ x₁) = π₀ (weaken x x₁)
weaken x (π₁ x₁) = π₁ (weaken x x₁)
weaken x (ι₀ x₁) = ι₀ (weaken x x₁)
weaken x (ι₁ x₁) = ι₁ (weaken x x₁)
weaken x (case x₁ x₂ x₃) = case (weaken x x₁) (weaken x x₂) (weaken x x₃)
weaken x (η' x₁) = η' (weaken x x₁)
weaken x (bind' x₁ x₂ x₃) = bind' x₁ (weaken x x₂) (weaken x x₃)

-- Substitution
var-subst : ∀{A C} (Γ Γ' : Ctx)
   → Exp Γ' A
   → C ∈ (Γ ++ [ A ] ++ Γ') 
   → Exp (Γ ++ Γ') C
var-subst [] Γ' x hd = x
var-subst [] Γ' x (tl x₁) = Var x₁
var-subst (x₂ ∷ Γ) Γ' x hd = Var hd
var-subst (x₂ ∷ Γ) Γ' x (tl x₁) = weaken tl (var-subst Γ Γ' x x₁)

tm-subst : ∀{A C} (Γ Γ' : Ctx) 
   → Exp Γ' A
   → Exp (Γ ++ [ A ] ++ Γ') C 
   → Exp (Γ ++ Γ') C 
tm-subst Γ Γ' x <>' = <>'
tm-subst Γ Γ' x (Var x₁) = var-subst Γ Γ' x x₁
tm-subst Γ Γ' x (λ' x₁) = λ' (tm-subst (_ ∷ Γ) Γ' x x₁)
tm-subst Γ Γ' x (x₁ ∙ x₂) = (tm-subst Γ Γ' x x₁) ∙ (tm-subst Γ Γ' x x₂)
tm-subst Γ Γ' x (pair x₁ x₂) = pair (tm-subst Γ Γ' x x₁) (tm-subst Γ Γ' x x₂)
tm-subst Γ Γ' x (π₀ x₁) = π₀ (tm-subst Γ Γ' x x₁)
tm-subst Γ Γ' x (π₁ x₁) = π₁ (tm-subst Γ Γ' x x₁)
tm-subst Γ Γ' x (ι₀ x₁) = ι₀ (tm-subst Γ Γ' x x₁)
tm-subst Γ Γ' x (ι₁ x₁) = ι₁ (tm-subst Γ Γ' x x₁)
tm-subst Γ Γ' x (case x₁ x₂ x₃) = case (tm-subst Γ Γ' x x₁) (tm-subst Γ Γ' x x₂) (tm-subst Γ Γ' x x₃)
tm-subst Γ Γ' x (η' x₁) = η' (tm-subst Γ Γ' x x₁)
tm-subst Γ Γ' x (bind' x₁ x₂ x₃) = bind' x₁ (tm-subst Γ Γ' x x₂) (tm-subst Γ Γ' x x₃)

subst : ∀{Γ A C} → Exp Γ A → Exp (A ∷ Γ) C → Exp Γ C
subst = tm-subst [] _

-- Reduction
data _⟶_ : ∀{Γ t} → Exp Γ t → Exp Γ t → Set where
  RApp₀  : ∀{Γ t₀ t₁} {e e' : Exp Γ (t₀ →' t₁)} {e₁ : Exp Γ t₀} 
         → e ⟶ e' → (e ∙ e₁) ⟶ (e' ∙ e₁)
  RApp₁  : ∀{Γ t₀ t₁} {e : Exp (t₀ ∷ Γ) t₁} {e₁ : Exp Γ t₀}
         → ((λ' e) ∙ e₁) ⟶ subst e₁ e
  RFst₀  : ∀{Γ t₀ t₁} {e e' : Exp Γ (t₀ ×' t₁)}
         → e ⟶ e' → π₀ e ⟶ π₀ e'
  RFst₁  : ∀{Γ t₀ t₁} {e₀ : Exp Γ t₀} {e₁ : Exp Γ t₁}
         → π₀ (pair e₀ e₁) ⟶ e₀
  RSnd₀  : ∀{Γ t₀ t₁} {e e' : Exp Γ (t₀ ×' t₁)}
         → e ⟶ e' → π₁ e ⟶ π₁ e'
  RSnd₁  : ∀{Γ t₀ t₁} {e₀ : Exp Γ t₀}{e₁ : Exp Γ t₁}
         → π₁ (pair e₀ e₁) ⟶ e₁
  Rcase₀ : ∀{Γ t₀ t₁ t₂} {e e' : Exp Γ (t₀ +' t₁)}{e₁ : Exp Γ (t₀ →' t₂)}{e₂ : Exp Γ (t₁ →' t₂)}
         → e ⟶ e' → case e e₁ e₂ ⟶ case e' e₁ e₂
  Rcase₁ : ∀{Γ t₀ t₁ t₂} {e : Exp Γ t₀}{e₁ : Exp Γ (t₀ →' t₂)}{e₂ : Exp Γ (t₁ →' t₂)}
         → case (ι₀ e) e₁ e₂ ⟶ (e₁ ∙ e)
  Rcase₂ : ∀{Γ t₀ t₁ t₂} {e : Exp Γ t₁}{e₁ : Exp Γ (t₀ →' t₂)}{e₂ : Exp Γ (t₁ →' t₂)}
         → case (ι₁ e) e₁ e₂ ⟶ (e₂ ∙ e)
  Rbind'₀ : ∀{Γ ℓ t₀ t₁} {p} {e e' : Exp Γ (T' ℓ t₀)} {e₁ : Exp Γ (t₀ →' t₁)}
         → e ⟶ e' → bind' p e e₁ ⟶ bind' p e' e₁
  Rbind'₁ : ∀{Γ ℓ t₀ t₁} {p} {e : Exp Γ t₀}{e₁ : Exp Γ (t₀ →' t₁)}
         → bind' p (η' {ℓ = ℓ} e) e₁ ⟶ (e₁ ∙ e)

{- Embedding in Agda -}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B} → A → B → A × B

fst : ∀{A B} → A × B → A
fst (x , x₁) = x

snd : ∀{A B} → A × B → B
snd (x , x₁) = x₁

data _+_ : Set → Set → Set where
  inl : {A B : Set} → A → A + B
  inr : {A B : Set} → B → A + B

caseOn : ∀{A B} → {C : Set} → (A + B) → (A → C) → (B → C) → C
caseOn (inl x) x₁ x₂ = x₁ x
caseOn (inr x) x₁ x₂ = x₂ x

data ⊤ : Set where
  <> : ⊤

record DCC : Set1 where
  field
    T : L → Set → Set
    prot : L → Set → Set
    η : {ℓ : L} {A : Set} → A → T ℓ A
    η-inj : ∀ {l A} {x y : A} -> η {l} x ≡ η y -> x ≡ y
    bind : {ℓ : L} {A B : Set} → prot ℓ B → T ℓ A → (A → B) → B
    ProtFlow : ∀ {t ℓ ℓ'} → ℓ ⊑ ℓ' → prot ℓ (T ℓ' t)
    ProtInner : ∀ {t ℓ ℓ'} → prot ℓ t → prot ℓ (T ℓ' t)
    ProtProduct : ∀ {t s ℓ} → prot ℓ t → prot ℓ s → prot ℓ (s × t)
    ProtFunction : ∀ {t s : Set}{ℓ} → prot ℓ t → prot ℓ (s → t)
    -- Monad laws
    bind-η : ∀{ℓ : L}{A B : Set}{p : prot ℓ B}{a : A}{k : A → B} → bind p (η a) k ≡ k a
