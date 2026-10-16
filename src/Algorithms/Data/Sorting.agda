module Algorithms.Data.Sorting where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Utilities using (all→head)
open import Data.Unit using (tt)



data Sorted : List ℕ → Set where
  sz : Sorted []
  so : ∀ (x : ℕ) → Sorted (x ∷ [])
  ss : ∀ (cur x : ℕ) → (xs : List ℕ) → Sorted (x ∷ xs) → cur ≤ x → Sorted (cur ∷ x ∷ xs)
