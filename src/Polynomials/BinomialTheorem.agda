module Polynomials.BinomialTheorem where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; cong₂)
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (foldr-map)
open import Series.Naturals using (naturalsᵣ)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (sa∸sa≡0)



{-
  Based on the beautiful recursive definition of combinations
  - that comes from Piṅgala's method to calculate long and short syllables in Sanskrit
    so writers of mantras could maintain perfect rhythmic vibration
  - which I think might have had a real utilitarian purpose
    as this was in a time (~200 BCE) when knowledge was passed on verbally
    thereby functioning as a natural error detection and correction mechanism
    and as a mnemonic device to maintain integrity of knowledge across generations

  How it works:
    suppose one wants to compute number of ways one could build a team of k players out of n people
    that is - 'pick n k'
    for any person p, one could pick p or not pick p
    suppose p is picked: now one needs to pick k-1 out of n-1, so recursively 'pick n-1 k-1'
    suppose p is not picked: now one still needs to pick k but out of n-1, so recursively 'pick n-1 k'
    because p must either be on the team or off the team, simply add those to get total ways
    that is → ⁿCₖ = ⁿ⁻¹Cₖ₋₁ + ⁿ⁻¹Cₖ
-}
pick : ℕ → ℕ → ℕ
pick zero _ = 1
pick (suc n) zero = 1
pick (suc n) (suc k) = (pick n k) + (pick n (suc k))



binomial-term : ℕ → ℕ → ℕ → ℕ → ℕ
binomial-term a b n k = (pick n k) * ((a ^ (n ∸ k)) * (b ^ k))



lemma-sum-*≡*-sum : ∀ (a : ℕ) (xs : List ℕ) → sum (map (a *_) xs) ≡ a * sum xs
lemma-sum-*≡*-sum a [] rewrite *-comm a (sum []) = refl
lemma-sum-*≡*-sum a (x ∷ xs) =
  begin
    sum (map (a *_) (x ∷ xs))
  ≡⟨⟩
    sum ((a * x) ∷ map (a *_) xs)
  ≡⟨⟩
    (a * x) + sum (map (a *_) xs)
  ≡⟨ cong ((a * x) +_) (lemma-sum-*≡*-sum a xs) ⟩
    (a * x) + (a * sum xs)
  ≡⟨ sym (*-distribˡ-+ a x (sum xs)) ⟩
    a * (x + sum xs)
  ≡⟨⟩
    a * sum (x ∷ xs)
  ∎



list-distrib : ∀ (a b : ℕ) (xs : List ℕ)
             → (a + b) * sum xs ≡ sum (map (a *_) xs) + sum (map (b *_) xs)
list-distrib a b [] rewrite *-comm (a + b) (sum []) = refl
list-distrib a b (x ∷ xs) =
  begin
    (a + b) * sum (x ∷ xs)
  ≡⟨ *-distribʳ-+ (sum (x ∷ xs)) a b ⟩
    (a * sum (x ∷ xs)) + (b * sum (x ∷ xs))
  ≡⟨ cong₂ (λ pa pb → pa + pb) (sym (lemma-sum-*≡*-sum a (x ∷ xs))) (sym (lemma-sum-*≡*-sum b (x ∷ xs))) ⟩
    sum (map (a *_) (x ∷ xs)) + sum (map (b *_) (x ∷ xs))
  ∎



--lemma-map-merge : ∀ (a : ℕ) (xs : List ℕ) → map (a *_)
{-
sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
≡ sum (map (λ k → a * (binomial-term a b n k)) (naturalsᵣ n))
≡ ⁿCₙ * a^1 * b^n +
  ⁿCₙ₋₁ * a^2 * b^n-1 +
  ... +
  ⁿC₀ * a^sn * b^0

sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
≡ ˢⁿCₙ * a^1 * b^n +
  ˢⁿCₙ₋₁ * a^2 * b^n-1 +
  ... +
  ˢⁿC₀ * a^sn * b^0
-}



{-
binomial-theorem : ∀ (a b n : ℕ)
                 → (a + b) ^ n
                 ≡ sum (map (λ k → binomial-term a b n k) (naturalsᵣ n))
binomial-theorem a b zero = refl
binomial-theorem a b (suc n) =
  begin
    (a + b) ^ suc n
  ≡⟨ refl ⟩
    (a + b) * ((a + b) ^ n)
  ≡⟨ cong ((a + b) *_) (binomial-theorem a b n) ⟩
    (a + b) * sum (map (λ k → binomial-term a b n k) (naturalsᵣ n))
  ≡⟨ list-distrib a b (map (λ k → binomial-term a b n k) (naturalsᵣ n)) ⟩
    sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n))) +
    sum (map (b *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
  ≡⟨ {!!} ⟩
    ((pick (suc n) (suc n)) * (b ^ suc n)) +
    sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ cong (_+ sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n)))
          (cong (λ x → (pick (suc n) (suc n)) * x) (sym (*-identityˡ (b ^ (suc n))))) ⟩
    ((pick (suc n) (suc n)) * (1 * (b ^ suc n))) +
    sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ refl ⟩
    ((pick (suc n) (suc n)) * ((a ^ 0) * (b ^ suc n))) +
    sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ cong (_+ sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n)))
          (cong (λ x → (pick (suc n) (suc n)) * ((a ^ x) * (b ^ suc n))) (sym (sa∸sa≡0 n))) ⟩
    ((pick (suc n) (suc n)) * ((a ^ (suc n ∸ suc n)) * (b ^ suc n))) +
    sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ refl ⟩
    (binomial-term a b (suc n) (suc n)) + sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ refl ⟩
    sum ((binomial-term a b (suc n) (suc n)) ∷ map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ refl ⟩
    sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ (suc n)))
  ∎
-}
