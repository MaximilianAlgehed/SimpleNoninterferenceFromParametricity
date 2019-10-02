open import Definitions
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Formalisation using (⊥; ex-falso)
open import Data.Star
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum

module Translation (dcc : DCC) where

open DCC dcc

-- Types
type : Type → Set
type unit      = ⊤
type (x →' x₂) = type x → type x₂
type (x ×' x₂) = type x × type x₂
type (x +' x₂) = type x + type x₂
type (T' ℓ x₂) = T ℓ (type x₂)

-- Environments
env : Ctx → Set
env [] = ⊤
env (x ∷ x₁) = type x × env x₁

index : ∀{Γ : Ctx}{t : Type} → t ∈ Γ → env Γ → type t
index hd (x , x₁) = x
index (tl p) (x , x₁) = index p x₁

protect-type : ∀{ℓ t} → ℓ ≼ t → prot ℓ (type t)
protect-type (PFlow x) = ProtFlow x
protect-type (PInner x) = ProtInner (protect-type x)
protect-type (PProduct x x₁) = ProtProduct (protect-type x) (protect-type x₁)
protect-type (PFunction x) = ProtFunction (protect-type x)

⟦_⟧ : ∀{Γ t} → Exp Γ t → env Γ → type t
⟦ Var x ⟧ γ = index x γ
⟦ λ' e ⟧ γ = λ z → ⟦ e ⟧ (z , γ)
⟦ e ∙ e₁ ⟧ γ = ⟦ e ⟧ γ (⟦ e₁ ⟧ γ)
⟦ pair e e₁ ⟧ γ = ⟦ e ⟧ γ , ⟦ e₁ ⟧ γ
⟦ π₀ e ⟧ γ = fst (⟦ e ⟧ γ)
⟦ π₁ e ⟧ γ = snd (⟦ e ⟧ γ)
⟦ ι₀ e ⟧ γ = inl (⟦ e ⟧ γ)
⟦ ι₁ e ⟧ γ = inr (⟦ e ⟧ γ)
⟦ case e e₁ e₂ ⟧ γ = caseOn (⟦ e ⟧ γ) (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ)
⟦ η' {ℓ = ℓ} e ⟧ γ = η (⟦ e ⟧ γ)
⟦ bind' x e e₁ ⟧ γ = bind (protect-type x) (⟦ e ⟧ γ) (⟦ e₁ ⟧ γ)
⟦ <>' ⟧ γ = <>

_++env_ : ∀{Γ Γ'} → env Γ → env Γ' → env (Γ ++ Γ')
_++env_ {[]} x x₁ = x₁
_++env_ {x₂ ∷ Γ} (x , x₃) x₁ = x , (x₃ ++env x₁)

postulate ext : ∀ {A B : Set} {f g : A -> B} -> (∀ z -> f z ≡ g z) -> f ≡ g

cong₃ : ∀{A B C D : Set} {x₀ y₀ : A} {x₁ y₁ : B} {x₂ y₂ : C} → (f : A → B → C → D)
      → x₀ ≡ y₀ → x₁ ≡ y₁ → x₂ ≡ y₂ → f x₀ x₁ x₂ ≡ f y₀ y₁ y₂
cong₃ f refl refl refl = refl

index-lemma : ∀{Γ Γ'}
            → (p : Superset Γ' Γ)
            → (t₀ : Type)
            → (z : type t₀)
            → (γ : env Γ)
            → (γ' : env Γ')
            → (∀{t}{x : t ∈ Γ} → index x γ ≡ index (p x) γ')
            → ∀{t}{x : t ∈ (t₀ ∷ Γ)} → index x (z , γ) ≡ index (Super-cons p x) (z , γ')
index-lemma p t₀ z γ γ' x {x = hd} = refl
index-lemma p t₀ z γ γ' x {x = tl x₁} = x

weaken-⟦⟧ : ∀{Γ Γ' t}
          → (γ : env Γ)
          → (γ' : env Γ')
          → (p : Superset Γ' Γ)
          → (∀{t}{x : t ∈ Γ} → index x γ ≡ index (p x) γ')
          → (e : Exp Γ t)
          → ⟦ e ⟧ γ ≡ ⟦ weaken p e ⟧ γ'
weaken-⟦⟧ γ γ' p t (Var x) = t
weaken-⟦⟧ γ γ' p t (λ' {t₀ = t₀} e) =
  ext λ z → weaken-⟦⟧ (z , γ) (z , γ') (Super-cons p) (λ {t'} {x'} → index-lemma p t₀ z γ γ' t {t'}{x'}) e
weaken-⟦⟧ γ γ' p t (e ∙ e₁) = cong₂ (λ f x → f x) (weaken-⟦⟧ γ γ' p t e) (weaken-⟦⟧ γ γ' p t e₁)
weaken-⟦⟧ γ γ' p t (pair e e₁) = cong₂ _,_ (weaken-⟦⟧ γ γ' p t e) (weaken-⟦⟧ γ γ' p t e₁)
weaken-⟦⟧ γ γ' p t (π₀ e) = cong fst (weaken-⟦⟧ γ γ' p t e)
weaken-⟦⟧ γ γ' p t (π₁ e) = cong snd (weaken-⟦⟧ γ γ' p t e)
weaken-⟦⟧ γ γ' p t (ι₀ e) = cong inl (weaken-⟦⟧ γ γ' p t e)
weaken-⟦⟧ γ γ' p t (ι₁ e) = cong inr (weaken-⟦⟧ γ γ' p t e)
weaken-⟦⟧ γ γ' p t (case e e₁ e₂) = cong₃ caseOn (weaken-⟦⟧ γ γ' p t e) (weaken-⟦⟧ γ γ' p t e₁) (weaken-⟦⟧ γ γ' p t e₂)
weaken-⟦⟧ γ γ' p t (η' e) = cong η (weaken-⟦⟧ γ γ' p t e)
weaken-⟦⟧ γ γ' p t (bind' x e e₁) = cong₂ (bind (protect-type x)) (weaken-⟦⟧ γ γ' p t e) (weaken-⟦⟧ γ γ' p t e₁)
weaken-⟦⟧ γ γ' p t <>' = refl

ok-var-subst : ∀{A C} (Γ Γ' : Ctx)(γ : env Γ)(γ' : env Γ')
             → (e₀ : Exp Γ' A)
             → (x : C ∈ (Γ ++ [ A ] ++ Γ'))
             → index x (γ ++env (⟦ e₀ ⟧ γ' , γ')) ≡ ⟦ var-subst Γ Γ' e₀ x ⟧ (γ ++env γ')
ok-var-subst [] Γ' γ γ' x hd = refl
ok-var-subst [] Γ' γ γ' x (tl x₁) = refl
ok-var-subst (x₂ ∷ Γ) Γ' (x₁ , x₃) γ' x hd = refl
ok-var-subst (x₂ ∷ Γ) Γ' (x₃ , γ) γ' x (tl x₁) =
  let ih = ok-var-subst Γ Γ' γ γ' x x₁ in
  trans ih (weaken-⟦⟧ (γ ++env γ') (x₃ , (γ ++env γ')) (λ {x₄} → tl) refl (var-subst Γ Γ' x x₁))

ok-tm-subst : ∀{A C} (Γ Γ' : Ctx)(γ : env Γ)(γ' : env Γ')
            → (e₀ : Exp Γ' A)
            → (e₁ : Exp (Γ ++ [ A ] ++ Γ') C)
            → ⟦ e₁ ⟧ (γ ++env (⟦ e₀ ⟧ γ' , γ')) ≡ ⟦ tm-subst Γ Γ' e₀ e₁ ⟧ (γ ++env γ')
ok-tm-subst Γ Γ' γ γ' e₀ (Var x) = ok-var-subst Γ Γ' γ γ' e₀ x
ok-tm-subst Γ Γ' γ γ' e₀ (λ' {t₀ = t₀} e₁) = ext (λ z → ok-tm-subst (t₀ ∷ Γ) Γ' (z , γ) γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (e₁ ∙ e₂) = cong₂ (λ f x → f x) (ok-tm-subst Γ Γ' γ γ' e₀ e₁) (ok-tm-subst Γ Γ' γ γ' e₀ e₂)
ok-tm-subst Γ Γ' γ γ' e₀ (pair e₁ e₂) = cong₂ _,_ (ok-tm-subst Γ Γ' γ γ' e₀ e₁) (ok-tm-subst Γ Γ' γ γ' e₀ e₂)
ok-tm-subst Γ Γ' γ γ' e₀ (π₀ e₁) = cong fst (ok-tm-subst Γ Γ' γ γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (π₁ e₁) = cong snd (ok-tm-subst Γ Γ' γ γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (ι₀ e₁) = cong inl (ok-tm-subst Γ Γ' γ γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (ι₁ e₁) = cong inr (ok-tm-subst Γ Γ' γ γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (case e₁ e₂ e₃) =
  cong₃ caseOn (ok-tm-subst Γ Γ' γ γ' e₀ e₁) (ok-tm-subst Γ Γ' γ γ' e₀ e₂) (ok-tm-subst Γ Γ' γ γ' e₀ e₃)
ok-tm-subst Γ Γ' γ γ' e₀ (η' e₁) = cong η (ok-tm-subst Γ Γ' γ γ' e₀ e₁)
ok-tm-subst Γ Γ' γ γ' e₀ (bind' x e₁ e₂) = cong₂ (bind (protect-type x)) (ok-tm-subst Γ Γ' γ γ' e₀ e₁) (ok-tm-subst Γ Γ' γ γ' e₀ e₂)
ok-tm-subst Γ Γ' γ γ' e₀ <>' = refl

ok : ∀{Γ t}{γ : env Γ}{e e' : Exp Γ t} → e ⟶ e' → ⟦ e ⟧ γ ≡ ⟦ e' ⟧ γ
ok {γ = γ} (RApp₀ {e = e} {e₁ = e₁} x) = cong (λ f → f (⟦ e₁ ⟧ γ)) (ok x)
ok {Γ} {γ = γ} (RApp₁ {e = e} {e₁}) = ok-tm-subst [] Γ <> γ e₁ e
ok (RFst₀ x) = cong fst (ok x)
ok RFst₁ = refl
ok (RSnd₀ x) = cong snd (ok x)
ok RSnd₁ = refl
ok (Rcase₀ x) = cong (λ c → caseOn c _ _) (ok x)
ok Rcase₁ = refl
ok Rcase₂ = refl
ok (Rbind'₀ x) = cong (λ s → bind _ s _) (ok x)
ok Rbind'₁ = bind-η

_⟶*_ : ∀{Γ t} → Exp Γ t → Exp Γ t → Set
_⟶*_ = Star _⟶_

ok-trans : ∀{Γ t}(γ : env Γ){e e' : Exp Γ t} → e ⟶* e' → ⟦ e ⟧ γ ≡ ⟦ e' ⟧ γ
ok-trans γ ε = refl
ok-trans γ (x ◅ p) = trans (ok x) (ok-trans γ p)

bool' = unit +' unit
true' : Exp [] bool'
true' = ι₀ <>'
false' : Exp [] bool'
false' = ι₁ <>'

postulate DCC-strongly-normalising : ∀ l -> (e : Exp [] (T' l bool')) -> (e ⟶* η' true') + (e ⟶* η' false')

_β≡_ : ∀{t} → Exp [] t → Exp [] t → Set
e₁ β≡ e₂ = ∃[ e ] (e₁ ⟶* e ∧ e₂ ⟶* e)

done : ∀ {l} -> η {l} (inr <>) ≡ η (inl <>) -> ⊥
done p with η-inj p
done p | ()

corro7 : ∀ l (e e' : Exp [] (T' l bool')) → ⟦ e ⟧ <> ≡ ⟦ e' ⟧ <> → e β≡ e'
corro7 l e e' p with DCC-strongly-normalising l e | DCC-strongly-normalising l e'
corro7 l e e' p | inl q | inl r = η' (ι₀ <>') , q , r
corro7 l e e' p | inr q | inr r = η' (ι₁ <>') , q , r
corro7 l e e' p | inr q | inl r rewrite ok-trans <> q | ok-trans <> r = ex-falso (done p)
corro7 l e e' p | inl q | inr r rewrite ok-trans <> q | ok-trans <> r = ex-falso (done (sym p))

Bool = ⊤ + ⊤
postulate lˆ : L

-- Note: here we drop the assumption that o satisfies its parametricity condition. (until Agda supports parametricity "well")
postulate noninterference : ∀{A} {l : L} {o : T l A → T lˆ Bool} → (a₀ a₁ : T l A) → (l ⊑ lˆ → ⊥) → o a₀ ≡ o a₁

Th8 :  forall l A a1 a2 -> (l ⊑ lˆ → ⊥) -> (e : Exp [] (T' l A →' T' lˆ bool')) -> (e ∙ a1) β≡ (e ∙ a2)
Th8 l A a1 a2 p e = corro7 lˆ (e ∙ a1) (e ∙ a2) (noninterference {type A} {l} {⟦ e ⟧ <>} (⟦ a1 ⟧ <>) (⟦ a2 ⟧ <>) p)
