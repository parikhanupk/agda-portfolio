module HardwareVerification.Bit where



open import Data.Nat using (ℕ)



data Bit : Set where
  low  : Bit
  high : Bit



valB : Bit → ℕ
valB low = 0
valB high = 1
