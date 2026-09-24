module Puzzles.MO-Romania-1959-fraction where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Nat.GCD using (GCD; gcd; gcd-GCD)
open Data.Nat.GCD.GCD renaming (base to gcd-base; step to gcd-step; sym to gcd-sym; unique to gcd-unique)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Data.List using (List; []; _∷_)



{-
   prove that the fraction (21n + 4) / (14n + 3) is irreducible for every natural number n
   in Agda:
a. ∀ n → GCD (21n + 4) (14n + 3) 1
b. ∀ n → gcd (21n + 4) (14n + 3) ≡ 1
-}



{-
  GCD n 1 1
→ GCD 1 n 1 (gcd-sym)
→ GCD 1 1+n 1 (gcd-step)
→ GCD 1+n 1 1 (gcd-sym)
-}
GCD-n-1-1 : ∀ (n : ℕ) → GCD n 1 1
GCD-n-1-1 zero = gcd-base
GCD-n-1-1 (suc n) = gcd-sym (gcd-step (gcd-sym (GCD-n-1-1 n)))



{-
  GCD 7n+1 1 1
→ GCD 7n+1 [7n+1]+1 1 (gcd-step)
→ GCD 7n+1 7n+2 1 (subst, +-assoc)
→ GCD 7n+2 7n+1 1 (gcd-sym)
-}
step-1 : ∀ (n : ℕ) → GCD (7 * n + 1) 1 1 → GCD (7 * n + 2) (7 * n + 1) 1
step-1 n gcd-[7n+1]-1-1 =
       gcd-sym (subst (λ x → GCD (7 * n + 1) x 1) (+-assoc (7 * n) 1 1) (gcd-step gcd-[7n+1]-1-1))



{-
  GCD 7n+2 7n+1 1
→ GCD 7n+1 7n+2 1 (gcd-sym)
→ GCD 7n+1 [7n+1]+[7n+2] 1 (gcd-step)
→ GCD 7n+1 14n+3 1 (subst, helper)
→ GCD 14n+3 7n+1 1 (gcd-sym)
-}
step-2 : ∀ (n : ℕ) → GCD (7 * n + 2) (7 * n + 1) 1 → GCD (14 * n + 3) (7 * n + 1) 1
step-2 n gcd-[7n+2]-[7n+1]-1 =
       gcd-sym (subst (λ x → GCD (7 * n + 1) x 1) (helper n) (gcd-step (gcd-sym gcd-[7n+2]-[7n+1]-1)))
       where
       helper : ∀ (n : ℕ) → (7 * n + 1) + (7 * n + 2) ≡ 14 * n + 3
       helper n = solve (n ∷ [])



{-
  GCD 14n+3 7n+1 1
→ GCD 14n+3 [14n+3]+[7n+1] 1 (gcd-step)
→ GCD 14n+3 21n+4 1 (subst, helper)
→ GCD 21n+4 14n+3 1 (gcd-sym)
-}
step-3 : ∀ (n : ℕ) → GCD (14 * n + 3) (7 * n + 1) 1 → GCD (21 * n + 4) (14 * n + 3) 1
step-3 n gcd-[14n+3]-[7n+1]-1 =
       gcd-sym (subst (λ x → GCD (14 * n + 3) x 1) (helper n) (gcd-step gcd-[14n+3]-[7n+1]-1))
       where
       helper : ∀ (n : ℕ) → (14 * n + 3) + (7 * n + 1) ≡ (21 * n + 4)
       helper n = solve (n ∷ [])



proof-a : ∀ (n : ℕ) → GCD (21 * n + 4) (14 * n + 3) 1
proof-a n = step-3 n (step-2 n (step-1 n (GCD-n-1-1 (7 * n + 1))))



proof-b : ∀ (n : ℕ) → gcd (21 * n + 4) (14 * n + 3) ≡ 1
proof-b n = gcd-unique (gcd-GCD (21 * n + 4) (14 * n + 3)) (proof-a n)
