module ScratchPad where



open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _^_)
open import Data.Nat.Properties using (+-comm)



a≤b→a≤[b+c] : ∀ a b c → a ≤ b → a ≤ (b + c)
a≤b→a≤[b+c] a b c z≤n = z≤n
a≤b→a≤[b+c] a b c (s≤s x) = s≤s (a≤b→a≤[b+c] _ _ c x)



1≤2ⁿ : ∀ n → 1 ≤ 2 ^ n
1≤2ⁿ zero = s≤s z≤n
1≤2ⁿ (suc n) rewrite +-comm (2 ^ n) zero = a≤b→a≤[b+c] 1 (2 ^ n) (2 ^ n) (1≤2ⁿ n)
