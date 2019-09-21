open import 00-abstract
open import 01-nats as ℕ using (ℕ ; Z ; S ; _+_ ; _*_ ; *-commutative ; *-associative)
open import Function using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Data.Product as Π using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as ∑ using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax)

record _∣_ (a : ℕ) (b : ℕ) : Set where
  constructor div-prf
  field
    k : ℕ
    eq : k * a ≡ b

everything-divides-0 : (x : ℕ) → x ∣ 0
everything-divides-0 x = div-prf 0 refl

only-0-divides-0 : (x : ℕ) → 0 ∣ x → x ≡ 0
only-0-divides-0 Z _ = refl
only-0-divides-0 (S x) Sx∣0 = ≡.trans (≡.sym $ _∣_.eq Sx∣0) cast
  where
  cast : _∣_.k Sx∣0 * 0 ≡ 0
  cast rewrite ℕ.*-rabsorb-0 (_∣_.k Sx∣0) = refl

div-antisym : (a b : ℕ) → a ∣ b → b ∣ a → a ≡ b
div-antisym Z Z a∣b b∣a = refl
div-antisym (S a) Z a∣b b∣a = only-0-divides-0 (S a) b∣a
div-antisym Z (S b) a∣b b∣a = ≡.sym $ only-0-divides-0 (S b) a∣b
div-antisym (S a′) (S b′) a∣b b∣a = cast $ _∣_.eq a∣b
  where
  a : ℕ
  a = S a′
  b : ℕ
  b = S b′
  k1 : ℕ
  k1 = _∣_.k a∣b
  k2 : ℕ
  k2 = _∣_.k b∣a
  eq1 : k1 * k2 * b ≡ b
  eq1 rewrite *-associative k1 k2 b | _∣_.eq b∣a = _∣_.eq a∣b
  test : k1 ≡ 1 × k2 ≡ 1
  test rewrite ≡.sym $ ℕ.*-rid-1 1 = ℕ.unit-product-property k1 k2 $ ℕ.*-cancellation (k1 * k2) 1 b′ eq1
  cast : k1 * a ≡ b → a ≡ b
  cast eq rewrite (proj₁ test) = eq

div-trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
div-trans a b c a∣b b∣c = div-prf (k2 * k1) $ cast $ _∣_.eq b∣c
  where
  k1 = _∣_.k a∣b
  k2 = _∣_.k b∣c
  cast : k2 * b ≡ c → k2 * k1 * a ≡ c
  cast eq rewrite ≡.sym $ _∣_.eq a∣b | *-associative k2 k1 a = eq

div-pord : PartialOrder ℕ _∣_
div-pord = record { po-refl = λ { a → div-prf 1 refl }
                  ; antisym = div-antisym
                  ; trans = div-trans }
