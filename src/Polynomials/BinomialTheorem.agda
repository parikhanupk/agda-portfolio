module Polynomials.BinomialTheorem where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-identityˡ; +-identityʳ; *-identityʳ; +-assoc)
open import Data.Nat.Properties using (m<n⇒m<1+n; n<1+n; n∸n≡0; +-comm; m+n∸n≡m; m≤n⇒m≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; cong₂)
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.List.Properties using (foldr-map; ++-identityʳ)
open import Series.Naturals using (naturalsᵣ)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (sa∸sa≡0; a≤a)
open import Data.Nat.Tactic.RingSolver using (solve)



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
    - if k = 0, there's only one way to build an empty team (by doing nothing)
    - if n = 0 but k > 0, there are no ways to build a team, none
    - if n > 0 and k > 0:
      for any person p, one could pick p or not pick p
      suppose p is picked: now one needs to pick k-1 out of n-1, so recursively 'pick n-1 k-1'
      suppose p is not picked: now one still needs to pick k but out of n-1, so recursively 'pick n-1 k'
      because p must either be on the team or off the team, simply add those to get total ways
      that is → ⁿCₖ = ⁿ⁻¹Cₖ₋₁ + ⁿ⁻¹Cₖ
-}
pick : ℕ → ℕ → ℕ
pick _ zero = 1
pick zero (suc _) = 0
pick (suc n) (suc k) = (pick n k) + (pick n (suc k))



pick-n-< : ∀ (n k : ℕ) → n < k → pick n k ≡ 0
pick-n-< zero (suc k) _ = refl
pick-n-< (suc n) (suc k) (s≤s n<k) =
  begin
    pick (suc n) (suc k)
  ≡⟨ refl ⟩
    pick n k + pick n (suc k)
  ≡⟨ cong (_+ pick n (suc k)) (pick-n-< n k n<k) ⟩
    0 + pick n (suc k)
  ≡⟨ refl ⟩
    pick n (suc k)
  ≡⟨ pick-n-< n (suc k) (m<n⇒m<1+n n<k) ⟩
    0
  ∎



pick-n-n : ∀ (n : ℕ) → pick n n ≡ 1
pick-n-n zero = refl
pick-n-n (suc n) =
  begin
    pick (suc n) (suc n)
  ≡⟨ refl ⟩
    (pick n n) + (pick n (suc n))
  ≡⟨ cong (_+ pick n (suc n)) (pick-n-n n) ⟩
    1 + (pick n (suc n))
  ≡⟨ cong (1 +_) (pick-n-< n (suc n) (n<1+n n)) ⟩
    1 + 0
  ≡⟨ refl ⟩
    1
  ∎



binomial-term : ℕ → ℕ → ℕ → ℕ → ℕ
binomial-term a b n k = (pick n k) * ((a ^ (n ∸ k)) * (b ^ k))



a*[b*[c*d]]≡b*[a*c*d] : ∀ (a b c d : ℕ) → (a * (b * (c * d))) ≡ b * (a * c * d)
a*[b*[c*d]]≡b*[a*c*d] a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])

a*[b*[c*d]]≡b*[c*[a*d]] : ∀ (a b c d : ℕ) → (a * (b * (c * d))) ≡ b * (c * (a * d))
a*[b*[c*d]]≡b*[c*[a*d]] a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])



k≤n→s[n∸k]≡sn∸k : ∀ (n k : ℕ) → k ≤ n → suc (n ∸ k) ≡ suc n ∸ k
k≤n→s[n∸k]≡sn∸k n zero _ = refl
k≤n→s[n∸k]≡sn∸k (suc n) (suc k) (s≤s k≤n) = k≤n→s[n∸k]≡sn∸k n k k≤n



lemma-binomial-merge : ∀ (a b n k : ℕ)
                     → (k≤n : k ≤ n)
                     → a * binomial-term a b (suc n) (suc k) +
                       b * binomial-term a b (suc n) k
                     ≡ binomial-term a b (suc (suc n)) (suc k)
lemma-binomial-merge a b n k k≤n =
  begin
    a * binomial-term a b (suc n) (suc k) +
    b * binomial-term a b (suc n) k
  ≡⟨ refl ⟩
    a * ((pick (suc n) (suc k)) * ((a ^ (suc n ∸ suc k)) * (b ^ suc k))) +
    b * ((pick (suc n) k) * ((a ^ (suc n ∸ k)) * (b ^ k)))
  ≡⟨ cong₂ (λ x y → x + y)
           (a*[b*[c*d]]≡b*[a*c*d] a (pick (suc n) (suc k)) (a ^ (suc n ∸ suc k)) (b ^ suc k))
           (a*[b*[c*d]]≡b*[c*[a*d]] b (pick (suc n) k) (a ^ (suc n ∸ k)) (b ^ k)) ⟩
    (pick (suc n) (suc k)) * (a * (a ^ (suc n ∸ suc k)) * (b ^ suc k)) +
    (pick (suc n) k) * ((a ^ (suc n ∸ k)) * (b * (b ^ k)))
  ≡⟨ refl ⟩
    (pick (suc n) (suc k)) * ((a ^ suc (n ∸ k)) * (b ^ suc k)) +
    (pick (suc n) k) * ((a ^ (suc n ∸ k)) * (b ^ suc k))
  ≡⟨ cong (λ x → (pick (suc n) (suc k)) * ((a ^ x) * (b ^ suc k)) + (pick (suc n) k) * ((a ^ (suc n ∸ k)) * (b ^ suc k)))
          (k≤n→s[n∸k]≡sn∸k n k k≤n) ⟩
    (pick (suc n) (suc k)) * ((a ^ (suc n ∸ k)) * (b ^ suc k)) +
    (pick (suc n) k) * ((a ^ (suc n ∸ k)) * (b ^ suc k))
  ≡⟨ sym (*-distribʳ-+ ((a ^ (suc n ∸ k)) * (b ^ suc k)) (pick (suc n) (suc k)) (pick (suc n) k)) ⟩
    ((pick (suc n) (suc k)) + (pick (suc n) k)) * ((a ^ (suc n ∸ k)) * (b ^ suc k))
  ≡⟨ cong (λ x → x * ((a ^ (suc n ∸ k)) * (b ^ suc k))) (+-comm (pick (suc n) (suc k)) (pick (suc n) k)) ⟩
    ((pick (suc n) k) + (pick (suc n) (suc k))) * ((a ^ (suc n ∸ k)) * (b ^ suc k))
  ≡⟨ refl ⟩
    pick (suc (suc n)) (suc k) * ((a ^ (suc n ∸ k)) * (b ^ suc k))
  ≡⟨ refl ⟩
    binomial-term a b (suc (suc n)) (suc k)
  ∎



binomial-term-n-0 : ∀ (a b n : ℕ) → binomial-term a b n 0 ≡ a ^ n
binomial-term-n-0 a b n =
  begin
    binomial-term a b n 0
  ≡⟨ refl ⟩
    (pick n 0) * ((a ^ (n ∸ 0)) * (b ^ 0))
  ≡⟨ refl ⟩
    1 * ((a ^ n) * 1)
  ≡⟨ *-identityˡ (a ^ n * 1) ⟩
    ((a ^ n) * 1)
  ≡⟨ *-identityʳ (a ^ n) ⟩
    a ^ n
  ∎



binomial-term-n-n : ∀ (a b n : ℕ) → binomial-term a b n n ≡ b ^ n
binomial-term-n-n a b n =
  begin
    binomial-term a b n n
  ≡⟨ refl ⟩
    (pick n n) * ((a ^ (n ∸ n)) * (b ^ n))
  ≡⟨ cong₂ (λ x y → x * (a ^ y * (b ^ n))) (pick-n-n n) (n∸n≡0 n) ⟩
    1 * ((a ^ 0) * (b ^ n))
  ≡⟨ refl ⟩
    1 * (1 * (b ^ n))
  ≡⟨ *-identityˡ (1 * (b ^ n)) ⟩
    (1 * (b ^ n))
  ≡⟨ *-identityˡ (b ^ n) ⟩
    b ^ n
  ∎



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



[a+b]+[c+d]≡[a+c]+[b+d] : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
[a+b]+[c+d]≡[a+c]+[b+d] a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])

[a+b]+[c+d]≡[b+c]+[a+d] : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (b + c) + (a + d)
[a+b]+[c+d]≡[b+c]+[a+d] a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])



map-merge : ∀ {A B C : Set}
           → (f : A → B)
           → (g : B → C)
           → (xs : List A)
           → map g (map f xs)
           ≡ map (λ x → g (f x)) xs
map-merge f g [] = refl
map-merge f g (x ∷ xs) =
  begin
    map g (map f (x ∷ xs))
  ≡⟨ refl ⟩
    map g (f x ∷ map f xs)
  ≡⟨ refl ⟩
    g (f x) ∷ map g (map f xs)
  ≡⟨ cong (g (f x) ∷_) (map-merge f g xs) ⟩
    g (f x) ∷ map (λ x → g (f x)) xs
  ≡⟨ refl ⟩
    map (λ x → g (f x)) (x ∷ xs)
  ∎



lemma : ∀ (a b n c : ℕ)
      → sum (map (c *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
      ≡ sum (map (λ k → c * binomial-term a b n k) (naturalsᵣ n))
lemma a b n c = cong sum (map-merge (λ k → binomial-term a b n k) (c *_) (naturalsᵣ n))



sum-map-merge : ∀ (f g : ℕ → ℕ)
              → (xs : List ℕ)
              → sum (map f xs) + sum (map g xs)
              ≡ sum (map (λ y → f y + g y) xs)
sum-map-merge f g [] = refl
sum-map-merge f g (x ∷ xs) =
  begin
    sum (map f (x ∷ xs)) + sum (map g (x ∷ xs))
  ≡⟨ refl ⟩
    sum (f x ∷ (map f xs)) + sum (g x ∷ (map g xs))
  ≡⟨ refl ⟩
    (f x + sum (map f xs)) + (g x + sum (map g xs))
  ≡⟨ [a+b]+[c+d]≡[a+c]+[b+d] (f x) (sum (map f xs)) (g x) (sum (map g xs)) ⟩
    (f x + g x) + (sum (map f xs) + sum (map g xs))
  ≡⟨ cong ((f x + g x) +_) (sum-map-merge f g xs) ⟩
    (f x + g x) + sum (map (λ y → f y + g y) xs)
  ≡⟨ refl ⟩
    sum (map (λ y → f y + g y) (x ∷ xs))
  ∎



sum-map-merge' : ∀ (f g h : ℕ → ℕ)
               → (f+g≡h : ∀ k → (f k + g k) ≡ h k)
               → (xs : List ℕ)
               → sum (map f xs) + sum (map g xs)
               ≡ sum (map h xs)
sum-map-merge' f g h f+g≡h [] = refl
sum-map-merge' f g h f+g≡h (x ∷ xs) =
  begin
    sum (map f (x ∷ xs)) + sum (map g (x ∷ xs))
  ≡⟨ refl ⟩
    sum (f x ∷ map f xs) + sum (g x ∷ map g xs)
  ≡⟨ refl ⟩
    (f x + sum (map f xs)) + (g x + sum (map g xs))
  ≡⟨ [a+b]+[c+d]≡[a+c]+[b+d] (f x) (sum (map f xs)) (g x) (sum (map g xs)) ⟩
    (f x + g x) + (sum (map f xs) + sum (map g xs))
  ≡⟨ cong ((f x + g x) +_) (sum-map-merge' f g h f+g≡h xs) ⟩
    (f x + g x) + sum (map h xs)
  ≡⟨ cong (_+ sum (map h xs)) (f+g≡h x) ⟩
    h x + sum (map h xs)
  ≡⟨ refl ⟩
    sum (map h (x ∷ xs))
  ∎



lemma-naturals : ∀ (n : ℕ) → (naturalsᵣ (suc n)) ≡ (map suc (naturalsᵣ n)) ++ (0 ∷ [])
lemma-naturals zero = refl
lemma-naturals (suc n) =
  begin
    naturalsᵣ (suc (suc n))
  ≡⟨ refl ⟩
    (suc (suc n)) ∷ naturalsᵣ (suc n)
  ≡⟨ cong (suc (suc n) ∷_) (lemma-naturals n) ⟩
    (suc (suc n)) ∷ (map suc (naturalsᵣ n)) ++ (0 ∷ [])
  ≡⟨ refl ⟩
    (map suc (naturalsᵣ (suc n))) ++ (0 ∷ [])
  ∎



lemma-3 : ∀ (f : ℕ → ℕ) → (n : ℕ)
        → sum (map f (map suc (naturalsᵣ n))) + (f 0)
        ≡ sum (map f (naturalsᵣ (suc n)))
lemma-3 f zero =
  begin
    sum (map f (map suc (naturalsᵣ zero))) + f 0
  ≡⟨ refl ⟩
    sum (map f (1 ∷ [])) + f 0
  ≡⟨ refl ⟩
    sum (f 1 ∷ []) + f 0
  ≡⟨ refl ⟩
    (f 1 + 0) + f 0
  ≡⟨ cong (_+ (f 0)) (+-identityʳ (f 1)) ⟩
    f 1 + f 0
  ≡⟨ cong (f 1 +_) (sym (+-identityʳ (f 0))) ⟩
    f 1 + (f 0 + 0)
  ≡⟨ refl ⟩
    f 1 + sum (f 0 ∷ [])
  ≡⟨ refl ⟩
    sum (f 1 ∷ (f 0 ∷ []))
  ≡⟨ refl ⟩
    sum (map f (naturalsᵣ 1))
  ∎
lemma-3 f (suc n) =
  begin
    sum (map f (map suc (naturalsᵣ (suc n)))) + f 0
  ≡⟨ refl ⟩
    sum (map f ((suc (suc n)) ∷ map suc (naturalsᵣ n))) + f 0
  ≡⟨ refl ⟩
    sum (f (suc (suc n)) ∷ map f (map suc (naturalsᵣ n))) + f 0
  ≡⟨ refl ⟩
    f (suc (suc n)) + sum (map f (map suc (naturalsᵣ n))) + f 0
  ≡⟨ +-assoc (f (suc (suc n))) (sum (map f (map suc (naturalsᵣ n)))) (f 0) ⟩
    f (suc (suc n)) + (sum (map f (map suc (naturalsᵣ n))) + f 0)
  ≡⟨ cong (λ x → f (suc (suc n)) + x) (lemma-3 f n) ⟩
    f (suc (suc n)) + sum (map f (naturalsᵣ (suc n)))
  ≡⟨ refl ⟩
    sum (map f (naturalsᵣ (suc (suc n))))
  ∎



lemma-map-++ : ∀ {A B : Set} → (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
lemma-map-++ f [] ys = refl
lemma-map-++ f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    map f (x ∷ (xs ++ ys))
  ≡⟨ refl ⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (lemma-map-++ f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨ refl ⟩
    map f (x ∷ xs) ++ map f ys
  ∎



lemma-sum-++ : ∀ (xs ys : List ℕ) → sum (xs ++ ys) ≡ (sum xs) + (sum ys)
lemma-sum-++ [] ys = refl
lemma-sum-++ (x ∷ xs) ys =
  begin
    sum ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    sum (x ∷ (xs ++ ys))
  ≡⟨ refl ⟩
    x + sum (xs ++ ys)
  ≡⟨ cong (x +_) (lemma-sum-++ xs ys) ⟩
    x + (sum xs + sum ys)
  ≡⟨ sym (+-assoc x (sum xs) (sum ys)) ⟩
    x + sum xs + sum ys
  ≡⟨ refl ⟩
    sum (x ∷ xs) + sum ys
  ∎



postulate
  func-lemma-binomial-merge : ∀ (a b n : ℕ)
                            → (λ k → a * binomial-term a b (suc n) (suc k) + b * binomial-term a b (suc n) k)
                            ≡ (λ k → binomial-term a b (suc (suc n)) (suc k))



{-
sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
≡ sum (map (λ k → a * (binomial-term a b n k)) (naturalsᵣ n))
≡ (ⁿCₙ * a¹ * bⁿ) + (ⁿCₙ₋₁ * a² * bⁿ⁻¹) + ... + (ⁿC₀ * aⁿ⁺¹ * b⁰)

sum (map (b *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
≡ sum (map (λ k → b * (binomial-term a b n k)) (naturalsᵣ n))
≡ (ⁿCₙ * a⁰ * bⁿ⁺¹) + (ⁿCₙ₋₁ * a¹ * bⁿ) + ... + (ⁿC₀ * aⁿ * b¹)

sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n))) +
sum (map (b *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
≡ (ⁿCₙ * a¹ * bⁿ) + (ⁿCₙ₋₁ * a² * bⁿ⁻¹) + ... + (ⁿC₀ * aⁿ⁺¹ * b⁰) +
  (ⁿCₙ * a⁰ * bⁿ⁺¹) + (ⁿCₙ₋₁ * a¹ * bⁿ) + ... + (ⁿC₀ * aⁿ * b¹)
≡ ((ⁿCₙ + ⁿCₙ₋₁) * a¹ * bⁿ) + ((ⁿCₙ₋₁ + ⁿCₙ₋₂) * a² * bⁿ⁻¹) + ... + ((ⁿC₁ + ⁿC₀) * aⁿ * b¹) +
  (ⁿC₀ * aⁿ⁺¹ * b⁰) + (ⁿCₙ * a⁰ * bⁿ⁺¹)
≡ ((ⁿCₙ + ⁿCₙ₋₁) * a¹ * bⁿ) + ((ⁿCₙ₋₁ + ⁿCₙ₋₂) * a² * bⁿ⁻¹) + ... + ((ⁿC₁ + ⁿC₀) * aⁿ * b¹) +
  aⁿ⁺¹ + bⁿ⁺¹

(pick (suc n) (suc n)) * a⁰ * bⁿ⁺¹
≡ (ⁿCₙ + ⁿCₙ₊₁) * a⁰ * bⁿ⁺¹

sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
≡ (ⁿ⁺¹Cₙ * a¹ * bⁿ) + (ⁿ⁺¹Cₙ₋₁ * a² * bⁿ⁻¹) + ... + (ⁿ⁺¹C₀ * aⁿ⁺¹ * b⁰)

((pick (suc n) (suc n)) * a⁰ * bⁿ⁺¹) +
sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
≡ (ⁿCₙ + ⁿCₙ₊₁) * a⁰ * bⁿ⁺¹ +
  (ⁿ⁺¹Cₙ * a¹ * bⁿ) + (ⁿ⁺¹Cₙ₋₁ * a² * bⁿ⁻¹) + ... + (ⁿ⁺¹C₀ * aⁿ⁺¹ * b⁰)

ⁿ⁺¹Cₙ = ⁿCₙ + ⁿCₙ₋₁
ⁿ⁺¹Cₙ₋₁ = ⁿCₙ₋₁ + ⁿCₙ₋₂
...
ⁿ⁺¹C₁ = ⁿC₁ + ⁿC₀
ⁿ⁺¹C₀ = 1

so, (ⁿCₙ + ⁿCₙ₊₁) * a⁰ * bⁿ⁺¹ +
    (ⁿ⁺¹Cₙ * a¹ * bⁿ) + (ⁿ⁺¹Cₙ₋₁ * a² * bⁿ⁻¹) + ... + (ⁿ⁺¹C₀ * aⁿ⁺¹ * b⁰)
≡   bⁿ⁺¹ + 
    ((ⁿCₙ + ⁿCₙ₋₁) * a¹ * bⁿ) + ((ⁿCₙ₋₁ + ⁿCₙ₋₂) * a² * bⁿ⁻¹) + ... + ((ⁿC₁ + ⁿC₀) * aⁿ * b¹) +
    aⁿ⁺¹

so,
((pick (suc n) (suc n)) * a⁰ * bⁿ⁺¹) +
sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
≡
sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n))) +
sum (map (b *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
-}
lemma-merge : ∀ (a b n : ℕ)
            → sum (map (a *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n))) +
              sum (map (b *_) (map (λ k → binomial-term a b n k) (naturalsᵣ n)))
            ≡ ((pick (suc n) (suc n)) * (b ^ suc n)) +
              sum (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ n))
lemma-merge a b zero =
  begin
    sum (map (a *_) (map (λ k → binomial-term a b zero k) (naturalsᵣ zero))) +
    sum (map (b *_) (map (λ k → binomial-term a b zero k) (naturalsᵣ zero)))
  ≡⟨ cong₂ (λ x y → x + y) (helper a a b) (helper b a b) ⟩
    a + b
  ≡⟨ solve (a ∷ b ∷ []) ⟩
    ((1 + 0) * (b * 1)) + ((1 * ((a * 1) * 1)) + 0)
  ≡⟨ refl ⟩
    (((pick 0 0) + (pick 0 1)) * (b * 1)) + ((1 * ((a * 1) * 1)) + 0)
  ≡⟨ refl ⟩
    ((pick 1 1) * (b * 1)) + ((1 * ((a * 1) * 1)) + 0)
  ≡⟨ refl ⟩
    ((pick 1 1) * (b * 1)) + sum ((1 * ((a * 1) * 1)) ∷ [])
  ≡⟨ refl ⟩
    ((pick 1 1) * (b * 1)) + sum (((pick 1 0) * ((a ^ 1) * (b ^ 0))) ∷ map (λ k → binomial-term a b 1 k) [])
  ≡⟨ refl ⟩
    ((pick 1 1) * (b * 1)) + sum (map (λ k → binomial-term a b 1 k) (0 ∷ []))
  ≡⟨ refl ⟩
    ((pick (suc zero) (suc zero)) * (b ^ suc zero)) +
    sum (map (λ k → binomial-term a b (suc zero) k) (naturalsᵣ zero))
  ∎
  where
  helper : ∀ (c d e : ℕ) → sum (map (c *_) (map (λ k → binomial-term d e zero k) (naturalsᵣ zero))) ≡ c
  helper c d e =
    begin sum (map (c *_) (map (λ k → binomial-term d e zero k) (naturalsᵣ zero)))
    ≡⟨ refl ⟩ sum (map (c *_) (map (λ k → binomial-term d e zero k) (0 ∷ [])))
    ≡⟨ refl ⟩ sum (map (c *_) ((binomial-term d e zero 0) ∷ map (λ k → binomial-term d e zero k) []))
    ≡⟨ refl ⟩ sum (map (c *_) ((binomial-term d e zero 0) ∷ []))
    ≡⟨ refl ⟩ sum (map (c *_) (((pick 0 0) * (d ^ 0 * e ^ 0)) ∷ []))
    ≡⟨ refl ⟩ sum (map (c *_) ((1 * (1 * 1)) ∷ []))
    ≡⟨ refl ⟩ sum (map (c *_) (1 ∷ []))
    ≡⟨ refl ⟩ sum ((c * 1) ∷ map (c *_) [])
    ≡⟨ refl ⟩ sum ((c * 1) ∷ [])
    ≡⟨ refl ⟩ ((c * 1) + 0)
    ≡⟨ +-identityʳ (c * 1) ⟩ (c * 1)
    ≡⟨ *-identityʳ c ⟩ c
    ∎
lemma-merge a b (suc n) =
  begin
    sum (map (a *_) (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ (suc n)))) +
    sum (map (b *_) (map (λ k → binomial-term a b (suc n) k) (naturalsᵣ (suc n))))
  ≡⟨ cong₂ (λ x y → x + y) (lemma a b (suc n) a) (lemma a b (suc n) b) ⟩
    sum (map (λ k → a * binomial-term a b (suc n) k) (naturalsᵣ (suc n))) +
    sum (map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ (suc n)))
  ≡⟨ cong (λ x → x + sum (map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ (suc n))))
          (sym (lemma-3 (λ k → a * binomial-term a b (suc n) k) n)) ⟩
    sum (map (λ k → a * binomial-term a b (suc n) k) (map suc (naturalsᵣ n))) + a * binomial-term a b (suc n) 0 +
    sum (b * binomial-term a b (suc n) (suc n) ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ cong₂ (λ x y → sum (map (λ k → a * binomial-term a b (suc n) k) (map suc (naturalsᵣ n))) + (a * x) +
                    sum (b * y ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n)))
          (binomial-term-n-0 a b (suc n))
          (binomial-term-n-n a b (suc n)) ⟩
    sum (map (λ k → a * binomial-term a b (suc n) k) (map suc (naturalsᵣ n))) + (a * a ^ (suc n)) +
    sum ((b * b ^ (suc n)) ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ cong (λ x → sum x + (a * a ^ (suc n)) +
                 sum ((b * b ^ (suc n)) ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n)))
          (map-merge suc (λ k → a * binomial-term a b (suc n) k) (naturalsᵣ n)) ⟩
    sum (map (λ l → (λ k → a * binomial-term a b (suc n) k) (suc l)) (naturalsᵣ n)) + (a * a ^ (suc n)) +
    sum ((b * b ^ (suc n)) ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ refl ⟩
    sum (map (λ k → a * binomial-term a b (suc n) (suc k)) (naturalsᵣ n)) + (a * a ^ (suc n)) +
    sum ((b * b ^ (suc n)) ∷ map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n))
  ≡⟨ [a+b]+[c+d]≡[b+c]+[a+d] (sum (map (λ k → a * binomial-term a b (suc n) (suc k)) (naturalsᵣ n)))
                             (a * a ^ suc n)
                             (b * b ^ suc n)
                             (sum (map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n))) ⟩
    ((a * a ^ (suc n)) + (b * b ^ (suc n))) +
    (sum (map (λ k → a * binomial-term a b (suc n) (suc k)) (naturalsᵣ n)) +
    sum (map (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n)))
  ≡⟨ cong (((a * a ^ (suc n)) + (b * b ^ (suc n))) +_)
          (sum-map-merge (λ k → a * binomial-term a b (suc n) (suc k)) (λ k → b * binomial-term a b (suc n) k) (naturalsᵣ n)) ⟩
    ((a * a ^ (suc n)) + (b * b ^ (suc n))) +
    (sum (map (λ k → (a * binomial-term a b (suc n) (suc k)) + (b * binomial-term a b (suc n) k)) (naturalsᵣ n)))
  ≡⟨ cong (λ f → ((a * a ^ (suc n)) + (b * b ^ (suc n))) + (sum (map f (naturalsᵣ n))))
          (func-lemma-binomial-merge a b n) ⟩
    ((a * a ^ (suc n)) + (b * b ^ (suc n))) +
    (sum (map (λ k → binomial-term a b (suc (suc n)) (suc k)) (naturalsᵣ n)))
  ≡⟨ refl ⟩
    ((a * a ^ (suc n)) + (b * b ^ (suc n))) +
    (sum (map (λ l → (λ k → binomial-term a b (suc (suc n)) k) (suc l)) (naturalsᵣ n)))
  ≡⟨ cong (((a * a ^ (suc n)) + (b * b ^ (suc n))) +_)
          (cong sum (sym (map-merge suc (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ n)))) ⟩
    ((a * a ^ (suc n)) + (b * b ^ (suc n))) +
    (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n))))
  ≡⟨ cong (λ x → x + (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))))
          (+-comm (a * a ^ (suc n)) (b * b ^ suc n)) ⟩
    ((b * b ^ (suc n)) + (a * a ^ (suc n))) +
    (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n))))
  ≡⟨ +-assoc (b * b ^ (suc n)) (a * a ^ suc n) (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))) ⟩
    (b * b ^ (suc n)) +
    ((a * a ^ (suc n)) + (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))))
  ≡⟨ refl ⟩
    (b * b ^ (suc n)) +
    ((a ^ (suc (suc n))) + (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))))
  ≡⟨ cong (b * b ^ (suc n) +_)
          (+-comm (a ^ (suc (suc n))) (sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n))))) ⟩
    (b * b ^ (suc n)) +
    ((sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))) + (a ^ (suc (suc n))))
  ≡⟨ cong (λ x → (b * b ^ (suc n)) + ((sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))) + x))
          (sym (binomial-term-n-0 a b (suc (suc n)))) ⟩
    (b * b ^ (suc n)) +
    ((sum (map (λ k → binomial-term a b (suc (suc n)) k) (map suc (naturalsᵣ n)))) + (binomial-term a b (suc (suc n)) 0))
  ≡⟨ cong (λ x → (b * b ^ (suc n)) + x) (lemma-3 (λ k → binomial-term a b (suc (suc n)) k) n) ⟩
    (b * b ^ (suc n)) + (sum (map (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ (suc n))))
  ≡⟨ cong (λ x → x + (sum (map (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ (suc n)))))
          (sym (*-identityˡ (b ^ suc (suc n)))) ⟩
    1 * (b ^ suc (suc n)) + sum (map (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ (suc n)))
  ≡⟨ cong (λ x → x * (b ^ suc (suc n)) + sum (map (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ (suc n))))
          (sym (pick-n-n (suc (suc n)))) ⟩
    (pick (suc (suc n)) (suc (suc n))) * (b ^ suc (suc n)) +
    sum (map (λ k → binomial-term a b (suc (suc n)) k) (naturalsᵣ (suc n)))
  ∎



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
  ≡⟨ lemma-merge a b n ⟩
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
