module Puzzles.n-eq-2n-implies-n-eq-0 where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; _≢_)
open import Data.Empty using (⊥-elim)



sa≡sb→a≡b : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
sa≡sb→a≡b refl = refl

a≡a+b→b≡0 : ∀ (a b : ℕ) → a ≡ a + b → b ≡ 0
a≡a+b→b≡0 _ zero _ = refl
a≡a+b→b≡0 (suc a) (suc b) sa≡s[a+sb] = a≡a+b→b≡0 a (suc b) (sa≡sb→a≡b sa≡s[a+sb])

n≡2n→n≡0 : ∀ (n : ℕ) → n ≡ 2 * n → n ≡ 0
n≡2n→n≡0 zero _ = refl
n≡2n→n≡0 (suc n) sn≡2sn rewrite +-identityʳ n = a≡a+b→b≡0 n (suc n) (sa≡sb→a≡b sn≡2sn)



--tried the same using infinite descent but can't be done in current form
--as n≡2n can't be derived from sn≡2sn
--so still using a≡a+b→b≡0
n≡2n→n≡0′ : ∀ (n : ℕ) → n ≡ 2 * n → n ≡ 0
n≡2n→n≡0′ zero _ = refl
n≡2n→n≡0′ (suc n) sn≡2sn =
  let
    n≡n+sn = trans (sa≡sb→a≡b sn≡2sn) (cong (λ x → n + suc x) (+-identityʳ n))
  in
    ⊥-elim (sn≢0 n (a≡a+b→b≡0 n (suc n) n≡n+sn))
  where
    sn≢0 : ∀ (n : ℕ) → suc n ≢ 0
    sn≢0 n ()
