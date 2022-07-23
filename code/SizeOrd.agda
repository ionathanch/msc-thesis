{-# OPTIONS --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂; Σ-syntax; _,_)
open import Function.Base using (_∘_)

variable
  ℓ ℓ′ : Level
  A C : Set ℓ
  B : A → Set ℓ

{- Sizes
  Defining sizes as a generalized form of Brouwer ordinals,
  with an order (see https://arxiv.org/abs/2104.02549)
-}

infix 30 ↑_
infix 30 ⊔_

data Size {ℓ} : Set (lsuc ℓ) where
  ↑_ : Size {ℓ} → Size
  ⊔_ : {A : Set ℓ} → (A → Size {ℓ}) → Size

data _≤_ {ℓ} : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ) where
  ↑s≤↑s : ∀ {r s} → r ≤ s → ↑ r ≤ ↑ s
  s≤⊔f  : ∀ {s} f (a : A) → s ≤ f a → s ≤ ⊔ f
  ⊔f≤s  : ∀ {s} f → (∀ (a : A) → f a ≤ s) → ⊔ f ≤ s

-- A possible definition of the smallest size
◯ : Size
◯ = ⊔ ⊥-elim

◯≤s : ∀ {s} → ◯ ≤ s
◯≤s = ⊔f≤s ⊥-elim λ ()

-- Reflexivity of ≤
s≤s : ∀ {s : Size {ℓ}} → s ≤ s
s≤s {s = ↑ s} = ↑s≤↑s s≤s
s≤s {s = ⊔ f} = ⊔f≤s f (λ a → s≤⊔f f a s≤s)

-- Transitivity of ≤
s≤s≤s : ∀ {r s t : Size {ℓ}} → r ≤ s → s ≤ t → r ≤ t
s≤s≤s (↑s≤↑s r≤s) (↑s≤↑s s≤t) = ↑s≤↑s (s≤s≤s r≤s s≤t)
s≤s≤s r≤s (s≤⊔f f a s≤fa) = s≤⊔f f a (s≤s≤s r≤s s≤fa)
s≤s≤s (⊔f≤s f fa≤s) s≤t = ⊔f≤s f (λ a → s≤s≤s (fa≤s a) s≤t)
s≤s≤s (s≤⊔f f a s≤fa) (⊔f≤s f fa≤t) = s≤s≤s s≤fa (fa≤t a)

-- Successor behaves as expected wrt ≤
s≤↑s : ∀ {s : Size {ℓ}} → s ≤ ↑ s
s≤↑s {s = ↑ s} = ↑s≤↑s s≤↑s
s≤↑s {s = ⊔ f} = ⊔f≤s f (λ a → s≤s≤s s≤↑s (↑s≤↑s (s≤⊔f f a s≤s)))

-- Strict order
_<_ : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ)
r < s = ↑ r ≤ s

{- Well-founded induction for Sizes via an
  accessibility predicate based on strict order
-}

record Acc (s : Size {ℓ}) : Set (lsuc ℓ) where
  inductive
  pattern
  constructor acc
  field acc< : (∀ r → r < s → Acc r)
open Acc

-- The accessibility predicate is a mere proposition
accIsProp : ∀ {s : Size {ℓ}} → (acc1 acc2 : Acc s) → acc1 ≡ acc2
accIsProp (acc p) (acc q) =
  cong acc (funext p q (λ r → funext (p r) (q r) (λ r<s → accIsProp (p r r<s) (q r r<s))))
  where postulate funext : ∀ (p q : ∀ x → B x) → (∀ x → p x ≡ q x) → p ≡ q

-- A size smaller or equal to an accessible size is still accessible
acc≤ : ∀ {r s : Size {ℓ}} → r ≤ s → Acc s → Acc r
acc≤ r≤s (acc p) = acc (λ t t<r → p t (s≤s≤s t<r r≤s))

-- All sizes are accessible
wf : ∀ (s : Size {ℓ}) → Acc s
wf (↑ s) = acc (λ { _ (↑s≤↑s r≤s) → acc≤ r≤s (wf s) })
wf (⊔ f) = acc (λ { r (s≤⊔f f a r<fa) → (wf (f a)).acc< r r<fa })

-- Well-founded induction:
-- If P holds on every smaller size, then P holds on this size
-- Recursion occurs structurally on the accessbility of sizes
wfInd : ∀ (P : Size {ℓ} → Set ℓ′) → (∀ s → (∀ r → r < s → P r) → P s) → ∀ s → P s
wfInd P f s = wfAcc s (wf s)
  where
  wfAcc : ∀ s → Acc s → P s
  wfAcc s (acc p) = f s (λ r r<s → wfAcc r (p r r<s))

{- W types
  W∞ is the full or "infinite" form, where there are no sizes;
  W is the bounded-sized form, parameterized by some Size,
  where constructors take a proof of smaller-sizedness
-}

data W∞ (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  sup∞ : ∀ a → (B a → W∞ A B) → W∞ A B

data W (A : Set ℓ) (B : A → Set ℓ) (s : Size {ℓ}) : Set (lsuc ℓ) where
  sup : ∀ r → r < s → (a : A) → (B a → W A B r) → W A B s

-- Eliminator for the W type based on wellfoundedness of sizes
elimW : (P : ∀ s → W A B s → Set ℓ′) →
  (p : ∀ s → (∀ r → r < s → (w : W A B r) → P r w) → (w : W A B s) → P s w) →
  ∀ s → (w : W A B s) → P s w
elimW P = wfInd (λ s → (w : W _ _ s) → P s w)

-- A full W∞ to a size-paired bounded-sized W form
findW : W∞ {ℓ} A B → Σ[ s ∈ Size ] W A B s
findW (sup∞ a f) =
  let s = ⊔ (proj₁ ∘ findW ∘ f)
  in ↑ s , sup s s≤s a ⊔f
  where
  ⊔f : _
  ⊔f b with proj₂ (findW (f b))
  ... | sup r r<s a g = sup r (s≤s≤s r<s (s≤⊔f (proj₁ ∘ findW ∘ f) b s≤s)) a g

-- The axiom of choice specialized to sized W types, "choosing" a size
ac : ∀ a → (B a → Σ[ s ∈ Size ] W A B s) → Σ[ s ∈ Size ] (B a → W A B s)
ac a f = ⊔ (proj₁ ∘ f) , f′
  where
  f′ : _
  f′ b with proj₂ (f b)
  ... | sup r r<s a f = sup r (s≤s≤s r<s (s≤⊔f _ b s≤s)) a f

-- Constructing a bounded-sized W out of the necessary pieces
mkW : ∀ a → (B a → Σ[ s ∈ Size ] W A B s) → Σ[ s ∈ Size ] W A B s
mkW a f =
  let sf = ac a f
  in ↑ proj₁ sf , sup (proj₁ sf) s≤s a (proj₂ sf)

{- Full inductives and infinite sizes -}

open import Agda.Builtin.Nat using (Nat; zero; suc)

limN : Nat → Size
limN zero = ◯
limN (suc n) = ↑ limN n

∞ᶰ : Size
∞ᶰ = ⊔ limN

limW : W∞ A B → Size
limW (sup∞ a f) = ⊔ λ b → limW (f b)

∞ʷ : ∀ {A : Set ℓ} {B : A → Set ℓ} → Size
∞ʷ {B = B} = ⊔ limW {B = B}