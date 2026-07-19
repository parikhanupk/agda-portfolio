module Naturals.Properties.Factorial where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Naturals.Factorial using (_!)



a+c<b+c : ∀ (a b c : ℕ) → a < b → a + c < b + c
a+c<b+c a b zero a<b
        rewrite +-identityʳ a
              | +-identityʳ b
              = a<b
a+c<b+c a b (suc c) a<b
        rewrite +-comm a (suc c)
              | +-comm b (suc c)
              | +-comm c a
              | +-comm c b
              = s≤s (a+c<b+c a b c a<b)



16<24 : 16 < 24
16<24 = a+c<b+c 0 8 16 (s≤s z≤n)



a<b+c : ∀ (a b c : ℕ) → a < b → a < b + c
a<b+c zero (suc b) c _ = s≤s z≤n
a<b+c (suc a) (suc b) c (s≤s a<b) = s≤s (a<b+c a b c a<b)



a+c<b+d : ∀ (a b c d : ℕ) → a < b → c < d → a + c < b + d
a+c<b+d zero zero c d () c<d
a+c<b+d zero (suc b) c d (s≤s a<b) c<d rewrite +-comm (suc b) d = a<b+c c d (suc b) c<d
a+c<b+d (suc a) zero c d () c<d
a+c<b+d (suc a) (suc b) c d (s≤s a<b) c<d = s≤s (a+c<b+d a b c d a<b c<d)



ac<bd : ∀ (a b c d : ℕ) → a < b → c < d → a * c < b * d
ac<bd zero zero c d () c<d
ac<bd zero (suc b) c (suc d) (s≤s a<b) (s≤s c≤d) = s≤s z≤n
ac<bd (suc a) zero c d () c<d
ac<bd (suc a) (suc b) c d (s≤s a<b) c<d = a+c<b+d c d (a * c) (b * d) c<d (ac<bd a b c d a<b c<d)



n≥4→2ⁿ<n! : ∀ (n : ℕ) → (2 ^ (4 + n)) < (4 + n) !
n≥4→2ⁿ<n! zero = 16<24
n≥4→2ⁿ<n! (suc n) = ac<bd 2 (5 + n) (2 ^ (4 + n)) ((4 + n) !) (s≤s (s≤s (s≤s z≤n))) (n≥4→2ⁿ<n! n)
