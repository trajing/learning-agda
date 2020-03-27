{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Function hiding (_⇔_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum as Σ using (_⊎_; inj₁; inj₂)
open import Data.Product as Π using (_×_; _,_; proj₁; proj₂)

_⇔_ : {m n : Level} → Set m → Set n → Set (m ⊔ n)
P ⇔ Q = (P → Q) × (Q → P)

contrapositive : {m n : Level} {P : Set m} {Q : Set n} → (P → Q) → ¬ Q → ¬ P
contrapositive x y = y ∘ x

curry : {m n k : Level} {P : Set m} {Q : Set n} {R : Set k} → ((P × Q) → R) → (P → Q → R)
curry f p q = f $ p , q

reverse-curry : {m n k : Level} {P : Set m} {Q : Set n} {R : Set k} → (P → Q → R) → (P × Q) → R
reverse-curry f pq = f (proj₁ pq) (proj₂ pq)

¬¬-intro : {n : Level} {P : Set n} → P → ¬ ¬ P
¬¬-intro p ¬p = ¬p p

¬¬¬-elim : {n : Level} {P : Set n} → ¬ ¬ ¬ P → ¬ P
¬¬¬-elim ¬¬¬p p = ¬¬¬p $ λ { ¬p → ¬p p }

negation-of-disjunction : {m n : Level} {P : Set m} {Q : Set n} → ¬ (P ⊎ Q) → ¬ P × ¬ Q
negation-of-disjunction ¬p⊎q = (λ { p → ¬p⊎q $ inj₁ p}) , λ { q → ¬p⊎q $ inj₂ q }

cast : ∀ {m n} → {A : Set m} {x y : A} {f : A → Set n} → x ≡ y → f x → f y
cast eq rewrite eq = id

record PartialOrder (A : Set) (_≤_ : A → A → Set) : Set where
  constructor pord-prf
  field
    po-refl : (a : A) → a ≤ a
    antisym : (a b : A) → a ≤ b → b ≤ a → a ≡ b
    trans : (a b c : A) → a ≤ b → b ≤ c → a ≤ c
