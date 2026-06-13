module HardwareVerification.Bit where



open import Data.Nat using (ℕ)



data Bit : Set where
  O : Bit
  I : Bit



valB : Bit → ℕ
valB O = 0
valB I = 1
