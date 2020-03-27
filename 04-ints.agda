open import 00-abstract
open import 01-nats as ℕ using (ℕ) renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _<_ to _ℕ<_)
open import 03-sign as S using (Sign)
open import Function using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Data.Product as Π using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as ∑ using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax)

data ℤ : Set where
  pos : ℕ → ℤ
  negsuc : ℕ → ℤ

_⊝_ : ℕ → ℕ → ℤ
x ⊝ 0 = pos x
0 ⊝ (ℕ.S x) = negsuc x
(ℕ.S x) ⊝ (ℕ.S y) = x ⊝ y

-_ : ℤ → ℤ
- (pos 0) = pos 0
- (pos (ℕ.S x)) = negsuc x
- (negsuc x) = pos (ℕ.S x)

_+_ : ℤ → ℤ → ℤ
(pos x) + (pos y) = pos $ x ℕ+ y
(negsuc x) + (negsuc y) = negsuc $ ℕ.S $ x ℕ+ y
(pos x) + (negsuc y) = x ⊝ (ℕ.S y)
(negsuc x) + (pos y) = y ⊝ (ℕ.S x)

_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

∣_∣ : ℤ → ℕ
∣ pos x ∣ = x
∣ negsuc x ∣ = ℕ.S x

sign : ℤ → Sign
sign (pos _) = S.+
sign (negsuc _) = S.-

_◃_ : Sign → ℕ → ℤ
_ ◃ 0 = pos 0
S.+ ◃ (ℕ.S x) = pos (ℕ.S x)
S.- ◃ (ℕ.S x) = negsuc x

◃-sound : (x : ℤ) → x ≡ (sign x) ◃ ∣ x ∣
◃-sound (pos 0) = refl
◃-sound (pos (ℕ.S x)) = refl
◃-sound (negsuc x) = refl

+◃-pos-coincide : (x : ℕ) → (S.+ ◃ x) ≡ pos x
+◃-pos-coincide 0 = refl
+◃-pos-coincide (ℕ.S x) = refl

_*_ : ℤ → ℤ → ℤ
x * y = ((sign x) S.* (sign y)) ◃ (∣ x ∣ ℕ* ∣ y ∣)

-- constants

0ℤ = S.+ ◃ 0
1ℤ = S.+ ◃ 1
-1ℤ = S.- ◃ 1

+-rid-0 : (x : ℤ) → (x + 0ℤ) ≡ x
+-rid-0 (pos x) rewrite ℕ.+-rid-0 x = refl
+-rid-0 (negsuc x) = refl

*-rid-1 : (x : ℤ) → (x * 1ℤ) ≡ x
*-rid-1 (pos x) rewrite ℕ.*-rid-1 x = +◃-pos-coincide x
*-rid-1 (negsuc x) rewrite ℕ.*-rid-1 x | ℕ.+-commutative x 1 = refl

*-rabsorb-0 : (x : ℤ) → (x * 0ℤ) ≡ 0ℤ
*-rabsorb-0 (pos x) rewrite ℕ.*-rabsorb-0 x = refl
*-rabsorb-0 (negsuc x) rewrite ℕ.*-rabsorb-0 x = refl

negation-involution : (x : ℤ) → - (- x) ≡ x
negation-involution (pos (ℕ.S _)) = refl
negation-involution (pos 0) = refl
negation-involution (negsuc _) = refl

n⊝n≡0 : (n : ℕ) → n ⊝ n ≡ 0ℤ
n⊝n≡0 0 = refl
n⊝n≡0 (ℕ.S n) rewrite n⊝n≡0 n = refl

+-linverse-- : (x : ℤ) → (- x) + x ≡ 0ℤ
+-linverse-- (pos (ℕ.S x)) rewrite n⊝n≡0 x = refl
+-linverse-- (pos 0) = refl
+-linverse-- (negsuc x) rewrite n⊝n≡0 x = refl

+-commutative : (x y : ℤ) → x + y ≡ y + x
+-commutative (pos x) (pos y) rewrite ℕ.+-commutative x y = refl
+-commutative (negsuc x) (negsuc y) rewrite ℕ.+-commutative x y = refl
+-commutative (pos x) (negsuc y) = refl
+-commutative (negsuc x) (pos y) = refl

*-commutative : (x y : ℤ) → x * y ≡ y * x
*-commutative (pos x) (pos y) rewrite ℕ.*-commutative x y = refl
*-commutative (negsuc x) (negsuc y) rewrite ℕ.*-commutative x y | ℕ.*-commutative' x y | ℕ.*-commutative' y x
                                          | ℕ.+-commutative' (x ℕ* y ℕ+ x) y | ℕ.+-commutative' (y ℕ* x ℕ+ y) x
                                          | ℕ.*-commutative x y | ≡.sym $ ℕ.+-associative (y ℕ* x) y x
                                          | ≡.sym $ ℕ.+-associative (y ℕ* x) x y | ℕ.+-commutative x y = refl
*-commutative (pos x) (negsuc y) rewrite ℕ.*-commutative x (ℕ.S y) = refl
*-commutative (negsuc x) (pos y) rewrite ℕ.*-commutative (ℕ.S x) y = refl

data _<_ : ℤ → ℤ → Set where
  negsuc-mono-dec : (a b : ℕ) → a ℕ< b → (negsuc b) < (negsuc a)
  neg-lt-pos : (a b : ℕ) → (negsuc a) < (pos b)
  pos-mono-inc : (a b : ℕ) → a ℕ< b → (pos a) < (pos b)

<-transitive : (x y z : ℤ) → x < y → y < z → x < z
<-transitive x y z x<y y<z = {!!}
