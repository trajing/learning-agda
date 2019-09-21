{-# OPTIONS --without-K #-}

open import 00-abstract
open import Function using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; refl)
open import Data.Empty
open import Relation.Nullary
open import Data.Product as Π using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as ∑ using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax)

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6  _+_
infixl 7  _*_

_+_ : ℕ → ℕ → ℕ
Z     + x = x
(S x) + y = S (x + y)

_*_ : ℕ → ℕ → ℕ
Z     * x = Z
(S x) * y = (x * y) + y

_^_ : ℕ → ℕ → ℕ
x ^ Z     = 1
x ^ (S y) = x * (x ^ y)

data _<_ : ℕ → ℕ → Set where
  <-base : {n : ℕ} → n < S n
  <-succ : {m n : ℕ} → m < n → m < S n

data _≈_ : ℕ → ℕ → Set where
  ≈-base : Z ≈ Z
  ≈-succ : {m n : ℕ} → n ≈ m → S n ≈ S m

≈-≡-coincide : {m n : ℕ} → (m ≈ n) ⇔ (m ≡ n)
≈-≡-coincide {Z} {n} = (λ { ≈-base → refl }) , (λ { refl → ≈-base })
≈-≡-coincide {S m} {n} = (λ { (≈-succ eq) → ≡.cong S $ proj₁ ≈-≡-coincide eq }) , (λ { refl → ≈-refl $ S m })
  where
  ≈-refl : (k : ℕ) → k ≈ k
  ≈-refl Z     = ≈-base
  ≈-refl (S k) = ≈-succ $ ≈-refl k

+-rid-0 : (x : ℕ) → x + 0 ≡ x
+-rid-0 Z = refl
+-rid-0 (S x) rewrite +-rid-0 x = refl

+-commutative' : (x y : ℕ) → x + S y ≡ S (x + y)
+-commutative' Z y = refl
+-commutative' (S x) y rewrite +-commutative' x y = refl

+-commutative : (x y : ℕ) → x + y ≡ y + x
+-commutative Z y rewrite +-rid-0 y = refl
+-commutative (S x) y rewrite +-commutative' y x | +-commutative x y = refl

+-associative : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-associative Z y z = refl
+-associative (S x) y z rewrite +-associative x y z = refl

S-cancellation : (x y : ℕ) → S x ≡ S y → x ≡ y
S-cancellation x y refl = refl

+-cancellation : (x y z : ℕ) → x + z ≡ y + z → x ≡ y
+-cancellation x y Z eq rewrite +-rid-0 x | +-rid-0 y = eq
+-cancellation x y (S z) eq rewrite +-commutative' x z | +-commutative' y z
  | +-cancellation x y z (S-cancellation (x + z) (y + z) eq) = refl

*-rabsorb-0 : (x : ℕ) → x * 0 ≡ 0
*-rabsorb-0 Z = refl
*-rabsorb-0 (S x) rewrite *-rabsorb-0 x = refl

*-rid-1 : (x : ℕ) → x * 1 ≡ x
*-rid-1 Z = refl
*-rid-1 (S x) rewrite *-rid-1 x | +-commutative x 1 = refl

*-commutative' : (x y : ℕ) → x * S y ≡ x * y + x
*-commutative' Z y = refl
*-commutative' (S x) y rewrite *-commutative' x y | ≡.sym $ +-associative (x * y) x (S y)
  | ≡.sym $ +-associative (x * y) y (S x) | +-commutative x (S y) | +-commutative y (S x)
  | +-commutative x y = refl
*-commutative : (x y : ℕ) → x * y ≡ y * x
*-commutative Z y rewrite *-rabsorb-0 y = refl
*-commutative (S x) y rewrite *-commutative' y x | *-commutative x y = refl

+-distribute-* : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
+-distribute-* Z y z = refl
+-distribute-* (S x) y z rewrite +-distribute-* x y z | ≡.sym $ +-associative (x * y) (x * z) (y + z)
                               | +-associative (x * z) y z | +-commutative (x * z) y | ≡.sym $ +-associative (x * y) y (x * z + z)
                               | +-associative y (x * z) z = refl

*-associative : (x y z : ℕ) → x * y * z ≡ x * (y * z)
*-associative Z y z = refl
*-associative (S x) y z rewrite *-commutative (x * y + y) z | +-distribute-* z (x * y) y | *-commutative z (x * y) | *-associative x y z | *-commutative y z = refl

*-cancellation : (x y z : ℕ) → x * S z ≡ y * S z → x ≡ y
*-cancellation Z Z z eq = refl
*-cancellation Z (S y) z eq rewrite +-commutative' (y * S z) z = absurd eq
  where
  absurd : {A : Set} {n : ℕ} → 0 ≡ S n → A
  absurd ()
*-cancellation (S x) Z z eq rewrite +-commutative' (x * S z) z = absurd eq
  where
  absurd : {A : Set} {n : ℕ} → S n ≡ 0 → A
  absurd ()
*-cancellation (S x) (S y) z eq = ≡.cong S $ *-cancellation x y z $ +-cancellation (x * S z) (y * S z) (S z) eq

unit-product-property : (x y : ℕ) → x * y ≡ 1 → x ≡ 1 × y ≡ 1
unit-product-property Z y ()
unit-product-property 1 y eq = refl , eq
unit-product-property (S (S x)) Z eq rewrite *-rabsorb-0 x = absurd eq
  where
  absurd : {A : Set} → 0 ≡ 1 → A
  absurd ()
unit-product-property (S (S x)) (S y) eq rewrite +-commutative' (x * S y + S y) y | ≡.sym $ +-associative (x * S y) (S y) y | +-commutative' (x * S y) (y + y) = absurd eq
  where
  absurd : {A : Set} {n : ℕ} → S (S n) ≡ 1 → A
  absurd ()

mutual
  data Even : ℕ → Set where
    0-even : Even 0
    S-odd-even : {n : ℕ} → Odd n → Even (S n)

  data Odd : ℕ → Set where
    S-even-odd : {n : ℕ} → Even n → Odd (S n)

even-2k : (n : ℕ) → Even n → Σ[ k ∈ ℕ ] 2 * k ≡ n
even-2k Z _ = record { fst = Z ; snd = refl }
even-2k (S (S n)) (S-odd-even (S-even-odd e)) = record { fst = fst ; snd = snd }
  where
  hyp : Σ[ k ∈ ℕ ] 2 * k ≡ n
  hyp = even-2k n e
  fst : ℕ
  fst = S $ proj₁ hyp
  snd : 2 * fst ≡ S (S n)
  snd rewrite +-commutative (proj₁ hyp) fst = ≡.cong (S ∘ S) $ proj₂ hyp

odd-2k+1 : (n : ℕ) → Odd n → Σ[ k ∈ ℕ ] 2 * k + 1 ≡ n
odd-2k+1 (S n) (S-even-odd e) = record { fst = fst ; snd = snd }
  where
  hyp : Σ[ k ∈ ℕ ] 2 * k ≡ n
  hyp = even-2k n e
  fst : ℕ
  fst = proj₁ hyp
  snd : 2 * fst + 1 ≡ S n
  snd rewrite ≡.sym $ +-associative fst fst 1 | +-commutative fst 1 | +-commutative' fst fst = ≡.cong S $ proj₂ hyp
