module Algorithms.Sorting.InsertionSort where



open import Data.Nat using (ℕ; zero; suc; _≤?_; _≤_; z≤n; s≤s; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤ᵇ⇒≤)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Algorithms.Data.Sorting using (Sorted)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool.ListAction using (all)
open import Data.Bool using (true; _∧_; false; T; Bool)
open import Data.Unit using (tt)
open import Data.Bool.Properties using (∧-identityʳ; T-≡)
open import Utilities using (rest→all; a≤a; all→head; all→rest)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)



insert : ℕ → List ℕ → List ℕ
insert cur [] = cur ∷ []
insert cur (x ∷ xs) with cur ≤? x
... | yes _ = cur ∷ (x ∷ xs)
... | no _ = x ∷ (insert cur xs)

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)



sx≤ᵇsy→x≤ᵇy : ∀ (x y : ℕ) → (suc x ≤ᵇ suc y) ≡ true → (x ≤ᵇ y) ≡ true
sx≤ᵇsy→x≤ᵇy zero zero _ = refl
sx≤ᵇsy→x≤ᵇy zero (suc y) _ = refl
sx≤ᵇsy→x≤ᵇy (suc x) (suc y) x≤ᵇy = x≤ᵇy

x≤ᵇy≡true→x≤y : ∀ (x y : ℕ) → (x ≤ᵇ y) ≡ true → x ≤ y
x≤ᵇy≡true→x≤y zero y _ = z≤n
x≤ᵇy≡true→x≤y (suc x) (suc y) x≤ᵇy = s≤s (x≤ᵇy≡true→x≤y x y (sx≤ᵇsy→x≤ᵇy x y x≤ᵇy))

sorted-head : ∀ (x : ℕ) → (xs : List ℕ) → all (x ≤ᵇ_) xs ≡ true → Sorted xs → Sorted (x ∷ xs)
sorted-head x [] all-x≤[] sorted-[] = Sorted.so x
sorted-head x (y ∷ xs) all-x≤y∷xs sorted-y∷xs = Sorted.ss x y xs sorted-y∷xs (x≤ᵇy≡true→x≤y x y (all→head (x ≤ᵇ_) y xs all-x≤y∷xs))

sorted-tail : ∀ (x : ℕ) → (xs : List ℕ) → Sorted (x ∷ xs) → Sorted xs
sorted-tail x [] (Sorted.so x) = Sorted.sz
sorted-tail cur (x ∷ xs) (Sorted.ss cur x xs sorted-x∷xs cur≤x) = sorted-x∷xs

lemma2 : ∀ (x y : ℕ) → (x ≤ᵇ y ) ≡ true → (x <ᵇ suc y) ≡ true
lemma2 zero y _ = refl
lemma2 (suc x) y x≤ᵇy = x≤ᵇy

lemma1 : ∀ (x y : ℕ) → x ≤ y → (x ≤ᵇ y) ≡ true
lemma1 zero y x≤y = refl
lemma1 (suc x) (suc y) (s≤s x≤y) = lemma2 x y (lemma1 x y x≤y)

lemma4 : ∀ (cur x : ℕ) → (xs : List ℕ) → Sorted (cur ∷ x ∷ xs) → cur ≤ x
lemma4 cur x xs (Sorted.ss cur x xs sorted-x∷xs cur≤x) = cur≤x

lemma3 : ∀ (x y : ℕ) → (xs : List ℕ) → x ≤ y → Sorted (y ∷ xs) → all (x ≤ᵇ_) (y ∷ xs) ≡ true
lemma3 x y [] x≤y sorted-y∷[] =
  begin
    all (_≤ᵇ_ x) (y ∷ [])
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (_≤ᵇ_ x) []
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ true
  ≡⟨ ∧-identityʳ (x ≤ᵇ y) ⟩
    (x ≤ᵇ y)
  ≡⟨ lemma1 x y x≤y ⟩
    true
  ∎
lemma3 x y (z ∷ xs) x≤y sorted-y∷z∷xs =
  begin
    all (_≤ᵇ_ x) (y ∷ z ∷ xs)
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ cong (λ b → b ∧ all (x ≤ᵇ_) (z ∷ xs)) (lemma1 x y x≤y) ⟩
    true ∧ all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ refl ⟩
    all (x ≤ᵇ_) (z ∷ xs)
  ≡⟨ lemma3 x z xs (≤-trans x≤y (lemma4 y z xs sorted-y∷z∷xs)) (sorted-tail y (z ∷ xs) sorted-y∷z∷xs) ⟩
    true
  ∎

lemma5 : ∀ (x y : ℕ) → (xs : List ℕ) → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ xs)
lemma5 x y [] x≤y (Sorted.so y) = Sorted.so x
lemma5 x y (z ∷ xs) x≤y (Sorted.ss y z xs p y≤z) = Sorted.ss x z xs p (≤-trans x≤y y≤z)

lemma : ∀ (cur x : ℕ) → (xs : List ℕ) → x ≤ cur → Sorted (x ∷ xs) → all (x ≤ᵇ_) (insert cur xs) ≡ true
lemma cur x [] x≤cur (Sorted.so x) =
  begin
    all (_≤ᵇ_ x) (insert cur [])
  ≡⟨ refl ⟩
    all (_≤ᵇ_ x) (cur ∷ [])
  ≡⟨ refl ⟩
    (x ≤ᵇ cur) ∧ all (_≤ᵇ_ x) []
  ≡⟨ refl ⟩
    (x ≤ᵇ cur) ∧ true
  ≡⟨ ∧-identityʳ (x ≤ᵇ cur) ⟩
    (x ≤ᵇ cur)
  ≡⟨ lemma1 x cur x≤cur ⟩
    true
  ∎
lemma cur x (y ∷ xs) x≤cur (Sorted.ss x y xs p x≤y) with cur ≤? y
... | yes cur≤y =
  begin
    all (x ≤ᵇ_) (cur ∷ y ∷ xs)
  ≡⟨ lemma3 x cur (y ∷ xs) x≤cur (Sorted.ss cur y xs p cur≤y) ⟩
    true
  ∎
... | no ¬cur≤y =
  begin
    all (x ≤ᵇ_) (y ∷ (insert cur xs))
  ≡⟨ refl ⟩
    (x ≤ᵇ y) ∧ all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ cong (λ b → b ∧ (all (x ≤ᵇ_) (insert cur xs))) (lemma1 x y x≤y) ⟩
    true ∧ all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ refl ⟩
    all (x ≤ᵇ_) (insert cur xs)
  ≡⟨ lemma cur x xs x≤cur (lemma5 x y xs x≤y p) ⟩
    true
  ∎

¬x≤y→y≤x : ∀ (x y : ℕ) → ¬ x ≤ y → y ≤ x
¬x≤y→y≤x zero zero _ = z≤n
¬x≤y→y≤x zero (suc y) ¬z≤s = ⊥-elim (¬z≤s z≤n)
¬x≤y→y≤x (suc x) zero _ = z≤n
¬x≤y→y≤x (suc x) (suc y) ¬sx≤sy = s≤s (¬x≤y→y≤x x y (λ x≤y → ¬sx≤sy (s≤s x≤y)))



insert-preserves-sortedness : ∀ (cur : ℕ) → (xs : List ℕ) → Sorted xs → Sorted (insert cur xs)
insert-preserves-sortedness cur [] sorted-[] = Sorted.so cur
insert-preserves-sortedness cur (x ∷ xs) sorted-x∷xs with cur ≤? x
... | yes cur≤x = Sorted.ss cur x xs sorted-x∷xs cur≤x
... | no ¬cur≤x = sorted-head x (insert cur xs) (lemma cur x xs (¬x≤y→y≤x cur x ¬cur≤x) sorted-x∷xs) (insert-preserves-sortedness cur xs (sorted-tail x xs sorted-x∷xs))



sort-correct : ∀ (xs : List ℕ) → Sorted (sort xs)
sort-correct [] = Sorted.sz
sort-correct (x ∷ xs) = insert-preserves-sortedness x (sort xs) (sort-correct xs)




insert-permutation : ∀ (x : ℕ) → (xs : List ℕ) → (insert x xs) ↭ x ∷ xs
insert-permutation x [] = _↭_.refl
insert-permutation x (y ∷ xs) with x ≤? y
... | yes t = _↭_.refl
... | no ¬t = _↭_.trans (_↭_.prep y (insert-permutation x xs)) (_↭_.swap y x _↭_.refl)

sort-permutation : ∀ (xs : List ℕ) → (sort xs) ↭ xs
sort-permutation [] = _↭_.refl
sort-permutation (x ∷ xs) = _↭_.trans (insert-permutation x (sort xs)) (_↭_.prep x (sort-permutation xs))
