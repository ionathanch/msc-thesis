{-# OPTIONS --sized-types #-}

open import Size

record Pair (S : SizeUniv) (T : S → Set) : Set where
  constructor _,_
  field
    size : S
    el : T size
open Pair

SizePair : (Size → Set) → Set
SizePair = Pair Size
syntax SizePair (λ s → T) = ∃[ s ] T

data ℕ (s : Size) : Set where
  zero : ∀ {r : Size< s} → ℕ s
  succ : ∀ {r : Size< s} → ℕ r → ℕ s

data Ord (s : Size) : Set where
  zero : ∀ {r : Size< s} → Ord s
  succ : ∀ {r : Size< s} → Ord r → Ord s
  lim  : ∀ {r : Size< s} → (∃[ t ] ℕ t → Ord r) → Ord s

ℕ→Ord : ∃[ t ] ℕ t → ∃[ s ] Ord s
ℕ→Ord (t , zero) = t , zero
ℕ→Ord (_ , succ {t} n) with ℕ→Ord (t , n)
... | s , o = (↑ s) , succ o

postulate
  limSize : ∀ {A : Set} → (A → Size) → Size
  ac : ∀ {A : Set} {B : Size → Set} → (A → ∃[ s ] B s) → ∃[ s ] (A → B s)
  -- ac f = limSize (λ a → size (f a)) , (λ a → el (f a))

ω : ∃[ s ] Ord s
ω with ac ℕ→Ord
... | s , f = (↑ s) , lim f