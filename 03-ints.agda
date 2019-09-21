open import 00-abstract
open import 01-nats as ℕ using (ℕ ; Z ; S ; *-commutative ; *-associative)
open import Function using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Data.Product as Π using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as ∑ using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax)

data ℤ : Set where
  pos : ℕ → ℤ
  negsuc : ℕ → ℤ

_+_ : ℤ → ℤ → ℤ
(pos x) + (pos y) = pos $ ℕ._+_ x y
(negsuc x) + (negsuc y) = negsuc $ S $ ℕ._+_ x y
