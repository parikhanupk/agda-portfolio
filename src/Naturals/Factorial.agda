module Naturals.Factorial where



open import Data.Nat using (ℕ; zero; suc; _*_)



_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * (n !)
