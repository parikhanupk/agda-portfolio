module Naturals.PosNat where



open import Data.Nat using (ℕ; zero; suc; _>_; _<_; NonZero; _≤_; z≤n; s≤s; _/_; _%_; _<ᵇ_; _+_; _*_; _^_)
open import Data.Nat.DivMod using (m/n<m)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (true)
open import Data.Bool.ListAction using (all)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Utilities using (all→rest)



fromℕ-helper : (b : ℕ) → (b>1 : b > 1) → (n : ℕ) → Acc _<_ n → (cur : List ℕ) → List ℕ
fromℕ-helper b b>1 zero _ cur = cur
fromℕ-helper b b>1 (suc n) (acc rs) cur =
  let
    instance
      _ : NonZero b
      _ = n>1→NonZero-n b>1
    q = (suc n) / b
    r = (suc n) % b
  in
    fromℕ-helper b b>1 q (rs (m/n<m (suc n) b b>1)) (r ∷ cur)
  where
    n>1→NonZero-n : {b : ℕ} → b > 1 → NonZero b
    n>1→NonZero-n (s≤s _) = record { nonZero = tt }

fromℕ : (b : ℕ) → (b>1 : b > 1) → (n : ℕ) → List ℕ
fromℕ b b>1 n = fromℕ-helper b b>1 n (<-wellFounded n) []



toℕ : (b : ℕ) → (b>1 : b > 1) → (digits : List ℕ) → (all (_<ᵇ b) digits ≡ true) → ℕ
toℕ b b>1 [] _ = 0
toℕ b b>1 (d ∷ digits) valid = ((b ^ (length digits)) * d)
                             + toℕ b b>1 digits (all→rest (_<ᵇ b) d digits valid)



{-
from-to-id : ∀ (b : ℕ) → (b>1 : b > 1)
             → (digits : List ℕ) → (digits<base : all (_<ᵇ b) digits ≡ true)
             → fromℕ b b>1 (toℕ b b>1 digits digits<base) ≡ digits
from-to-id b b>1 digits digits<base = {!!}
-}
