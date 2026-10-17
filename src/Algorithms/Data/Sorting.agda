module Algorithms.Data.Sorting where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (true; _∧_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Utilities using (all→head)



data Sorted-≤ : List ℕ → Set where
  sz : Sorted-≤ []
  so : ∀ (x : ℕ) → Sorted-≤ (x ∷ [])
  ss : ∀ (cur x : ℕ) → (xs : List ℕ) → Sorted-≤ (x ∷ xs) → cur ≤ x → Sorted-≤ (cur ∷ x ∷ xs)



sx≤ᵇsy→x≤ᵇy : ∀ (x y : ℕ) → (suc x ≤ᵇ suc y) ≡ true → (x ≤ᵇ y) ≡ true
sx≤ᵇsy→x≤ᵇy zero y _ = refl
sx≤ᵇsy→x≤ᵇy (suc x) (suc y) sx≤ᵇsy = sx≤ᵇsy

x≤ᵇy→x≤y : ∀ (x y : ℕ) → (x ≤ᵇ y) ≡ true → x ≤ y
x≤ᵇy→x≤y zero y _ = z≤n
x≤ᵇy→x≤y (suc x) (suc y) sx≤ᵇsy = s≤s (x≤ᵇy→x≤y x y (sx≤ᵇsy→x≤ᵇy x y sx≤ᵇsy))



sorted-cons : ∀ (x : ℕ) → (xs : List ℕ) → all (x ≤ᵇ_) xs ≡ true → Sorted-≤ xs → Sorted-≤ (x ∷ xs)
sorted-cons x [] _ _ = so x
sorted-cons x (y ∷ xs) all-x≤y∷xs sorted-≤-y∷xs = ss x y xs sorted-≤-y∷xs (x≤ᵇy→x≤y x y (all→head (x ≤ᵇ_) y xs all-x≤y∷xs))



sorted-tail : ∀ (x : ℕ) → (xs : List ℕ) → Sorted-≤ (x ∷ xs) → Sorted-≤ xs
sorted-tail x [] _ = sz
sorted-tail cur (x ∷ xs) (ss cur x xs sorted-≤-x∷xs cur≤x) = sorted-≤-x∷xs



sorted-head-swap : ∀ (x y : ℕ) → (xs : List ℕ) → x ≤ y → Sorted-≤ (y ∷ xs) → Sorted-≤ (x ∷ xs)
sorted-head-swap x y [] _ _ = so x
sorted-head-swap x y (z ∷ xs) x≤y (ss y z xs sorted-≤-z∷xs y≤z) = ss x z xs sorted-≤-z∷xs (≤-trans x≤y y≤z)



x≤ᵇy→x<ᵇsy : ∀ (x y : ℕ) → (x ≤ᵇ y ) ≡ true → (x <ᵇ suc y) ≡ true
x≤ᵇy→x<ᵇsy zero y _ = refl
x≤ᵇy→x<ᵇsy (suc x) y x<ᵇy = x<ᵇy

≤→≤ᵇ : ∀ (x y : ℕ) → x ≤ y → (x ≤ᵇ y) ≡ true
≤→≤ᵇ zero y _ = refl
≤→≤ᵇ (suc x) (suc y) (s≤s x≤y) = x≤ᵇy→x<ᵇsy x y (≤→≤ᵇ x y x≤y)

sorted-ss-inv : ∀ (cur x : ℕ) → (xs : List ℕ) → Sorted-≤ (cur ∷ x ∷ xs) → cur ≤ x
sorted-ss-inv cur x xs (ss cur x xs sorted-≤-x∷xs cur≤x) = cur≤x

sorted→all : ∀ (x y : ℕ) → (xs : List ℕ) → x ≤ y → Sorted-≤ (y ∷ xs) → all (x ≤ᵇ_) (y ∷ xs) ≡ true
sorted→all x y [] x≤y _ =
  begin
    all (_≤ᵇ_ x) (y ∷ [])
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (_≤ᵇ_ x) []
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ true
  ≡⟨ ∧-identityʳ (x ≤ᵇ y) ⟩
    (x ≤ᵇ y)
  ≡⟨ ≤→≤ᵇ x y x≤y ⟩
    true
  ∎
sorted→all x y (z ∷ xs) x≤y sorted-≤-y∷z∷xs =
  begin
    all (_≤ᵇ_ x) (y ∷ z ∷ xs)
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ cong (λ b → b ∧ all (x ≤ᵇ_) (z ∷ xs)) (≤→≤ᵇ x y x≤y) ⟩
    true ∧ all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ refl ⟩
    all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ sorted→all x z xs (≤-trans x≤y (sorted-ss-inv y z xs sorted-≤-y∷z∷xs)) (sorted-tail y (z ∷ xs) sorted-≤-y∷z∷xs) ⟩
    true
  ∎
