{- A note on the formalisation:
    We use the names `Sec` and `S` in this formalisation
    but the formalisation covers the entire paper including the
    `DCC` language.
-}
module Formalisation where
open import Relation.Binary.PropositionalEquality

data Bool : Set where
  true : Bool
  false : Bool

data ⊥ : Set where

ex-falso : ⊥ -> {A : Set} -> A
ex-falso ()

data _+_ (A : Set) (B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

record ⊤ : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

Σ-syntax : (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : (A : Set) (B : Set) → Set
A × B = Σ[ x ∈ A ] B

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : (A -> ⊥) -> Dec A

⋆ = Set


⟦⋆⟧ : Set -> Set -> Set1
⟦⋆⟧ A B = A -> B -> Set

_⟦×⟧_ : forall {A0 A1} (P : ⟦⋆⟧ A0 A1) {B0 B1} (Q : ⟦⋆⟧ B0 B1) -> ⟦⋆⟧ (A0 × B0) (A1 × B1)
(P ⟦×⟧ Q) (a0 , b0) (a1 , b1) = P a0 a1 × Q b0 b1

⟦⋆1⟧ : Set1 -> Set1 -> Set2
⟦⋆1⟧ A B = A -> B -> Set1

_⟦→⟧_ : {A1 A2 : Set} -> ⟦⋆⟧ A1 A2 -> {B1 B2 : Set} -> ⟦⋆⟧ B1 B2 -> (A1 -> B1) -> (A2 -> B2) -> Set
(A ⟦→⟧ B) f g = ∀ x y -> A x y -> B (f x) (g y)

_⟦1→⟧_ : {A1 A2 : Set1} -> ⟦⋆1⟧ A1 A2 -> {B1 B2 : Set} -> ⟦⋆⟧ B1 B2 -> (A1 -> B1) -> (A2 -> B2) -> Set1
(A ⟦1→⟧ B) f g = ∀ x y -> A x y -> B (f x) (g y)

_⟦1→1⟧_ : {A1 A2 : Set1} -> ⟦⋆1⟧ A1 A2 -> {B1 B2 : Set1} -> ⟦⋆1⟧ B1 B2 -> (A1 -> B1) -> (A2 -> B2) -> Set1
(A ⟦1→1⟧ B) f g = ∀ x y -> A x y -> B (f x) (g y)

⟦Bool⟧ : ⟦⋆⟧ Bool Bool
⟦Bool⟧ = _≡_

infixr 1 _⟦→⟧_

module X
     (L : Set)
     (lˆ : L)
     (_⊑_ : L -> L -> Set)
     (trans⊑ : ∀{x y z} -> x ⊑ y -> y ⊑ z -> x ⊑ z)
     (ref⊑ : ∀{x} → x ⊑ x)
     (_⊑?_ : ∀ x y -> Dec (x ⊑ y))
  where


  _̸⊑_ : L -> L -> Set
  l1 ̸⊑ l2 = (l1 ⊑ l2) -> ⊥


  record Sec : Set1 where
    field
      S : L -> ⋆ -> ⋆
      up : ∀ {l l'} a -> l ⊑ l' -> S l a -> S l' a
      bind : ∀{l a b} -> S l a -> (a -> S l b) -> S l b
      return : ∀{l a} -> a -> S l a
      _⪯_ : (l : L) -> Set -> Set
      map : {A B : ⋆} → (l : L) → (A → B) → S l A → S l B
      join : (l : L) → (A : ⋆) → l ⪯ A → S l A → A
      protectS : forall l l' A -> l ⊑ l' -> l ⪯ S l' A
      protectS' : forall l l' A -> l ⪯ A -> l ⪯ S l' A
      protect× : forall l A B -> l ⪯ A -> l ⪯ B -> l ⪯ (A × B)
      protect→ : forall l (A B : Set) -> l ⪯ B -> l ⪯ (A → B)

    bindDCC : (l : L) → (A B : ⋆) → l ⪯ B → S l A → (A → B) → B
    bindDCC l A B p a k =  join l B p (map l k a)

    standardBind : (l : L) → (A B : Set) → S l A → (A → S l B) → S l B 
    standardBind l A B s k = bindDCC l A (S l B) (protectS l l B ref⊑) s k

  sec : Sec
  sec = record
    { S = λ _ A → A ;
      up = λ a p x → x ;
      bind = λ x x₁ → x₁ x ;
      return = λ x → x ;
      _⪯_ = λ l A → ⊤ ; -- because S l A = A (unfortunately an Agda record isn't a module in that we can't use previous definitions)
      join = λ l A p a → a ;
      protectS = λ l l' A _ → tt ; 
      protectS' = λ l l' A _ → tt ;
      protect× = λ l A B _ _ → tt ; 
      protect→ = λ l A B _ → tt ;
      map = λ l z → z
      }

  open Sec sec

  ⟦S⟧ : (l : L) → {A0 A1 : ⋆} → (RA : A0 → A1 → ⋆) → S l A0 → S l A1 → ⋆
  ⟦S⟧ l RA a0 a1 = (l ⊑ lˆ) → RA a0 a1

  upR : ∀ {l l'} {A0 A1} -> (RA : ⟦⋆⟧ A0 A1) -> (p : l ⊑ l') -> (⟦S⟧ l RA ⟦→⟧ ⟦S⟧ l' RA) (up A0 p) (up A1 p)
  upR RA p x y q r = q (trans⊑ p r)


  _⟦⪯⟧_ : (l : L) → {A0 A1 : ⋆} → (RA : A0 → A1 → ⋆) → l ⪯ A0 → l ⪯ A1 → ⋆
  _⟦⪯⟧_ l {A0} {A1} RA p0 p1 = l ̸⊑ lˆ -> (a0 : A0) → (a1 : A1) → RA a0 a1

  bindR : (l : L) → {A0 A1 : ⋆} → (RA : A0 → A1 → ⋆) →
                      {B0 B1 : ⋆} → (RB : B0 → B1 → ⋆) →
             (⟦S⟧ l RA ⟦→⟧ (RA ⟦→⟧ ⟦S⟧ l RB) ⟦→⟧ ⟦S⟧ l RB) (bind {l}) (bind {l})
  bindR l RA RB x y x₁ x₂ y₁ x₃ x₄ = x₃ x y (x₁ x₄) x₄

  returnR : (l : L) → {A0 A1 : ⋆} → (RA : A0 → A1 → ⋆) →
            (RA ⟦→⟧ ⟦S⟧ l RA) (return {l}) (return {l})
  returnR l RA x y z _ = z

  ⟦protectS⟧ : forall l l' → (A0 : ⋆) → (A1 : ⋆) → (RA : ⟦⋆⟧ A0 A1) → (p : l ⊑ l') →  (l ⟦⪯⟧ (⟦S⟧ l' RA)) (protectS l l' A0 p) (protectS l l' A1 p)
  ⟦protectS⟧ = λ l l' A0 A1 RA p q a0 a1 r → ex-falso (q (trans⊑ p r))

  ⟦protectS'⟧ : forall l l' → (A0 : ⋆) → (A1 : ⋆) → (RA : ⟦⋆⟧ A0 A1) → ((l ⟦⪯⟧ RA) ⟦→⟧  (l ⟦⪯⟧ (⟦S⟧ l' RA))) (protectS' l l' A0) (protectS' l l' A1)
  ⟦protectS'⟧ = λ l l' A0 A1 RA p0 p1 pR q a0 a1 r → pR q a0 a1

  ⟦protect×⟧ : forall l → {A0 A1 : ⋆} → (RA : ⟦⋆⟧ A0 A1) → {B0 B1 : ⋆} → (RB : ⟦⋆⟧ B0 B1) →
               ((l ⟦⪯⟧ RA) ⟦→⟧ (l ⟦⪯⟧ RB) ⟦→⟧ (l ⟦⪯⟧ (RA ⟦×⟧ RB))) (protect× l A0 B0) (protect× l A1 B1)
  ⟦protect×⟧ l RA RB p0 p1 pR q0 q1 qR r (a0 , b0) (a1 , b1) = (pR r a0 a1) , (qR r b0 b1)

  ⟦protect→⟧ : forall l → {A0 A1 : ⋆} → (RA : ⟦⋆⟧ A0 A1) → {B0 B1 : ⋆} → (RB : ⟦⋆⟧ B0 B1) →
               ((l ⟦⪯⟧ RB) ⟦→⟧ (l ⟦⪯⟧ (RA ⟦→⟧ RB))) (protect→ l A0 B0) (protect→ l A1 B1)
  ⟦protect→⟧ l RA RB p0 p1 pR r f0 f1 x₁ y₁ x₂ = pR r (f0 x₁) (f1 y₁)

  ⟦join⟧ : (l : L) → {A0 A1 : ⋆} → (RA : ⟦⋆⟧ A0 A1) → (l ⟦⪯⟧ RA ⟦→⟧ ⟦S⟧ l RA ⟦→⟧ RA) (join l A0) (join l A1)
  ⟦join⟧ l RA p0 p1 Rp a0 a1 aR with l ⊑? lˆ
  ⟦join⟧ l RA p0 p1 Rp a0 a1 aR | yes x = aR x
  ⟦join⟧ l RA p0 p1 Rp a0 a1 aR | no x = Rp x a0 a1


  ⟦map⟧ : {A0 A1 : ⋆} → (RA : ⟦⋆⟧ A0 A1) →
          {B0 B1 : ⋆} → (RB : ⟦⋆⟧ B0 B1) →
          (l : L) → ((RA ⟦→⟧ RB) ⟦→⟧ ⟦S⟧ l RA ⟦→⟧ ⟦S⟧ l RB) (map l) (map l)
  ⟦map⟧ = λ RA RB l x y x₁ x₂ y₁ x₃ x₄ → x₁ x₂ y₁ (x₃ x₄)

  -- We have to add `⟦o⟧` as an assumption, because parametricity is not internalised
  -- in Agda
  -- (Theorem 3 in paper)
  noninterference : ∀{A} {⟦A⟧ : ⟦⋆⟧ A A} {l : L} {o : S l A → S l Bool} → (⟦o⟧ : (⟦S⟧ l ⟦A⟧ ⟦→⟧ ⟦S⟧ lˆ ⟦Bool⟧) o o) → (b₀ b₁ : S l A)
                  → (l ⊑ lˆ → ⊥) → o b₀ ≡ o b₁
  noninterference x b₀ b₁ x₁ = x b₀ b₁ (λ p → ex-falso (x₁ p)) ref⊑
