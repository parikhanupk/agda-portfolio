module Naturals.PosNat where



open import Data.Nat using (ℕ; zero; suc; _>_; _<_; NonZero; _≤_; z≤n; s≤s; _/_; _%_; _<ᵇ_; _+_; _*_; _^_)
open import Data.Nat.DivMod using (m/n<m; m%n<n)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (true)
open import Data.Bool.ListAction using (all)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Utilities using (all→rest; <→<ᵇ; rest→all)



data PosNat (b : ℕ) (p : b > 1) : Set where
  posNat : (digits : List ℕ)
         → (valid : all (_<ᵇ b) digits ≡ true)
         → PosNat b p



module _ (b : ℕ) (p : b > 1) where

  fromℕ-helper : (n : ℕ) → Acc _<_ n → PosNat b p → PosNat b p
  fromℕ-helper zero _ cur = cur
  fromℕ-helper (suc n) (acc rs) (posNat digits valid) =
    let
      instance
        _ : NonZero b
        _ = n>1→NonZero-n p
      q = (suc n) / b
      r = (suc n) % b

      r<b : r < b
      r<b = m%n<n (suc n) b

      new-acc = rs (m/n<m (suc n) b p)
      new-valid = rest→all (_<ᵇ b) (suc n % b) digits (<→<ᵇ r<b) valid
    in
      fromℕ-helper q new-acc (posNat (r ∷ digits) new-valid)
    where
      n>1→NonZero-n : {n : ℕ} → n > 1 → NonZero n
      n>1→NonZero-n (s≤s _) = record { nonZero = tt }

  fromℕ : (n : ℕ) → PosNat b p
  fromℕ n = fromℕ-helper n (<-wellFounded n) (posNat [] refl)

  --needed as PosNat is a record type and Agda's termination checker doesn't see the terminating behavior
  toℕ-helper : List ℕ → ℕ
  toℕ-helper [] = 0
  toℕ-helper (d ∷ digits) = ((b ^ length digits) * d) + toℕ-helper digits

  toℕ : PosNat b p → ℕ
  toℕ (posNat digits _) = toℕ-helper digits
