module Puzzles.Consecutive-product-of-3-div-by-6 where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_)
open import Divisibility.RuleB using (Div; dz; ds; da→db→d[a+b]; da→d[a*b])
open import Puzzles.nnn+11n-is-div-by-6 using (n³+11n-is-div-by-6)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (_²; _³; a²≡a*a; a³≡a*a*a)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Data.List using (List; []; _∷_)



Div6 = Div 6 (s≤s z≤n)



sn*ssn*sssn≡6[1+n²]+[n³+11n] : ∀ (n : ℕ)
                             → (suc n) * (suc (suc n)) * (suc (suc (suc n)))
                             ≡ (6 * (1 + n ²)) + (n ³ + (11 * n))
sn*ssn*sssn≡6[1+n²]+[n³+11n] n =
  begin
    suc n * suc (suc n) * suc (suc (suc n))
  ≡⟨ solve (n ∷ []) ⟩
    6 * (1 + (n * n)) + ((n * n * n) + (11 * n))
  ≡⟨ cong₂ (λ x y → 6 * (1 + x) + (y + (11 * n))) (sym (a²≡a*a n)) (sym (a³≡a*a*a n)) ⟩
    6 * (1 + (n ²)) + ((n ³) + (11 * n))
  ∎



n*sn*ssn-is-div-6 : ∀ (n : ℕ) → Div6 (n * (suc n) * (suc (suc n)))
n*sn*ssn-is-div-6 zero = dz
n*sn*ssn-is-div-6 (suc n) =
                  subst Div6
                        (sym (sn*ssn*sssn≡6[1+n²]+[n³+11n] n))
                        (da→db→d[a+b] (s≤s z≤n)
                                      (da→d[a*b] {6} {6} {1 + n ²} (s≤s z≤n) (ds dz))
                                      (n³+11n-is-div-by-6 n))
