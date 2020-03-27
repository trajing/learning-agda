open import 01-nats as ℕ using (ℕ ; S)

data Vec {n} : Set n → ℕ → Set n where
  vempty : ∀ {A n} → Vec A n
  vappend : ∀ {A n} → A → Vec A n → Vec A (S n)

data List {n} : Set n → Set n where
  [] : ∀ {A} → List A
  _∷_ : ∀ {A} → A → List A → List A

data BTree {n} : Set n → Set n where
  leaf : ∀ {A} → A → BTree A
  node : ∀ {A} → BTree A → BTree A → BTree A

