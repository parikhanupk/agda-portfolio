module Data.Power where



open import Data.Nat using (ℕ; zero; suc; _*_; _^_)



data Pow (p : ℕ) : ℕ → Set where
  po : Pow p 1
  pn : ∀ {n : ℕ} → Pow p n → Pow p (p * n)



pbⁿ : ∀ (b n : ℕ) → Pow b (b ^ n)
pbⁿ b zero = po
pbⁿ b (suc n) = pn (pbⁿ b n)
