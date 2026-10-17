module Algorithms.Sorting.InsertionSort where



open import Data.Nat using (ℕ; zero; suc; _≤?_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Algorithms.Data.Sorting using (Sorted-≤; sorted-tail; sorted-cons; sorted-head-swap; ≤→≤ᵇ; sorted→all)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (true; _∧_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Bool.ListAction using (all)
open import Utilities using (¬x≤y→y≤x)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)



insert : ℕ → List ℕ → List ℕ
insert cur [] = cur ∷ []
insert cur (x ∷ xs) with cur ≤? x
... | yes _ = cur ∷ (x ∷ xs)
... | no _ = x ∷ (insert cur xs)

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)



lemma : ∀ (cur x : ℕ) → (xs : List ℕ) → x ≤ cur → Sorted-≤ (x ∷ xs) → all (x ≤ᵇ_) (insert cur xs) ≡ true
lemma cur x [] x≤cur (Sorted-≤.so x) =
  begin
    all (x ≤ᵇ_) (insert cur [])
  ≡⟨ refl ⟩
    all (x ≤ᵇ_) (cur ∷ [])
  ≡⟨ refl ⟩
    (x ≤ᵇ cur) ∧ all (x ≤ᵇ_) []
  ≡⟨ refl ⟩
    (x ≤ᵇ cur) ∧ true
  ≡⟨ ∧-identityʳ (x ≤ᵇ cur) ⟩
    (x ≤ᵇ cur)
  ≡⟨ ≤→≤ᵇ x cur x≤cur ⟩
    true
  ∎
lemma cur x (y ∷ xs) x≤cur (Sorted-≤.ss x y xs sorted-≤-y∷xs x≤y) with cur ≤? y
... | yes cur≤y =
  begin
    all (x ≤ᵇ_) (cur ∷ y ∷ xs)
  ≡⟨ sorted→all x cur (y ∷ xs) x≤cur (Sorted-≤.ss cur y xs sorted-≤-y∷xs cur≤y) ⟩
    true
  ∎
... | no ¬cur≤y =
  begin
    all (x ≤ᵇ_) (y ∷ (insert cur xs))
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ cong (λ b → b ∧ (all (x ≤ᵇ_) (insert cur xs))) (≤→≤ᵇ x y x≤y) ⟩
    true ∧ all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ refl ⟩
    all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ lemma cur x xs x≤cur (sorted-head-swap x y xs x≤y sorted-≤-y∷xs) ⟩
    true
  ∎



insert-preserves-sortedness : ∀ (cur : ℕ) → (xs : List ℕ) → Sorted-≤ xs → Sorted-≤ (insert cur xs)
insert-preserves-sortedness cur [] _ = Sorted-≤.so cur
insert-preserves-sortedness cur (x ∷ xs) sorted-≤-x∷xs with cur ≤? x
... | yes cur≤x = Sorted-≤.ss cur x xs sorted-≤-x∷xs cur≤x
... | no ¬cur≤x = sorted-cons x
                              (insert cur xs)
                              (lemma cur x xs (¬x≤y→y≤x cur x ¬cur≤x) sorted-≤-x∷xs)
                              (insert-preserves-sortedness cur xs (sorted-tail x xs sorted-≤-x∷xs))



sort-correct : ∀ (xs : List ℕ) → Sorted-≤ (sort xs)
sort-correct [] = Sorted-≤.sz
sort-correct (x ∷ xs) = insert-preserves-sortedness x (sort xs) (sort-correct xs)



insert-permutation : ∀ (x : ℕ) → (xs : List ℕ) → (insert x xs) ↭ x ∷ xs
insert-permutation x [] = _↭_.refl
insert-permutation x (y ∷ xs) with x ≤? y
... | yes t = _↭_.refl
... | no ¬t = _↭_.trans (_↭_.prep y (insert-permutation x xs)) (_↭_.swap y x _↭_.refl)



sort-permutation : ∀ (xs : List ℕ) → (sort xs) ↭ xs
sort-permutation [] = _↭_.refl
sort-permutation (x ∷ xs) = _↭_.trans (insert-permutation x (sort xs)) (_↭_.prep x (sort-permutation xs))
