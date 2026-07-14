module Naturals.Fibonacci where



open import Data.Nat using (ℕ; zero; suc; _+_)



fib : ℕ → ℕ
fib zero = 0
fib (suc zero) = 1
fib (suc (suc n)) = (fib (suc n)) + (fib n)
