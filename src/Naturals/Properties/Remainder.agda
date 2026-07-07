module Naturals.Properties.Remainder where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-comm; *-assoc; *-distribˡ-+; *-distribʳ-+; +-comm; +-assoc)
open import Utilities using (_²)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Naturals.Properties.EvenOdd using (Even; Odd; eo; es; os)
open import Data.Product using (∃-syntax; _,_)
open import Polynomials.Binomials using ([a+b]²≡a²+2ab+b²)



n²≡4k→[2+n]²≡4[1+n+k] : ∀ {n k} → n ² ≡ k * 4 → (2 + n) ² ≡ (1 + n + k) * 4
n²≡4k→[2+n]²≡4[1+n+k] {n} {k} n²≡k*4 =
  begin
    (2 + n) ²
  ≡⟨ [a+b]²≡a²+2ab+b² 2 n ⟩
    4 + (2 * (2 * n)) + n ²
  ≡⟨ cong (λ x → 4 + x + n ²) (sym (*-assoc 2 2 n)) ⟩
    (4 * 1) + (4 * n) + n ²
  ≡⟨ cong (λ x → x + n ²) (sym (*-distribˡ-+ 4 1 n)) ⟩
    4 * (1 + n) + n ²
  ≡⟨ cong (λ x → 4 * (1 + n) + x) n²≡k*4 ⟩
    4 * (1 + n) + k * 4
  ≡⟨ cong (λ x → x + k * 4) (*-comm 4 (1 + n)) ⟩
    (1 + n) * 4 + k * 4
  ≡⟨ sym (*-distribʳ-+ 4 (1 + n) k) ⟩
    (1 + n + k) * 4
  ∎

even-n→n²%4≡0 : ∀ {n : ℕ} → Even n → ∃[ k ](n ² ≡ k * 4)
even-n→n²%4≡0 {.(zero)} eo = zero , refl
even-n→n²%4≡0 {.(suc (suc n'))} (es (os {n'} even-n'))
  with even-n→n²%4≡0 even-n'
...  | k , n²≡k*4 = (1 + n' + k) , n²≡4k→[2+n]²≡4[1+n+k] {n'} {k} n²≡k*4
{-
    (suc (suc n))²
  ≡ (2 + n)²
  ≡ 4 + 4n + n²
  ≡ (4 * (1 + n)) + (k * 4)
  ≡ ((1 + n) * 4) + (k * 4)
  ≡ (1 + n + k) * 4
-}

n²≡4k→[2+n]²≡4[1+n+k]+1 : ∀ {n k} → n ² ≡ 1 + (k * 4) → (2 + n) ² ≡ 1 + ((1 + n + k) * 4)
n²≡4k→[2+n]²≡4[1+n+k]+1 {n} {k} n²≡[k*4]+1 =
  begin
    (2 + n) ²
  ≡⟨ [a+b]²≡a²+2ab+b² 2 n ⟩
    4 + (2 * (2 * n)) + n ²
  ≡⟨ cong (λ x → 4 + x + n ²) (sym (*-assoc 2 2 n)) ⟩
    (4 * 1) + (4 * n) + n ²
  ≡⟨ cong (λ x → x + n ²) (sym (*-distribˡ-+ 4 1 n)) ⟩
    4 * (1 + n) + n ²
  ≡⟨ cong (λ x → 4 * (1 + n) + x) n²≡[k*4]+1 ⟩
    4 * (1 + n) + (1 + (k * 4))
  ≡⟨ cong (λ x → 4 * (1 + n) + x) (+-comm 1 (k * 4)) ⟩
    4 * (1 + n) + ((k * 4) + 1)
  ≡⟨ sym (+-assoc (4 * (1 + n)) (k * 4) 1) ⟩
    (4 * (1 + n) + (k * 4)) + 1
  ≡⟨ cong (λ x → (x + (k * 4)) + 1) (*-comm 4 (1 + n)) ⟩
    (((1 + n) * 4) + (k * 4)) + 1
  ≡⟨ cong (λ x → x + 1) (sym (*-distribʳ-+ 4 (1 + n) k)) ⟩
    ((1 + n + k) * 4) + 1
  ≡⟨ +-comm ((1 + n + k) * 4) 1 ⟩
    1 + ((1 + n + k) * 4)
  ∎

odd-n→n²%4≡1 : ∀ {n : ℕ} → Odd n → ∃[ k ](n ² ≡ 1 + (k * 4))
odd-n→n²%4≡1 {.(suc zero)} (os eo) = zero , refl
odd-n→n²%4≡1 {.(suc (suc n'))} (os (es {n'} odd-n'))
  with odd-n→n²%4≡1 odd-n'
...  | k , n²≡1+[k*4] = (1 + n' + k) , n²≡4k→[2+n]²≡4[1+n+k]+1 {n'} {k} n²≡1+[k*4]
{-
    (suc (suc n))²
  ≡ (2 + n)²
  ≡ 4 + 4n + n²
  ≡ (4 * (1 + n)) + (1 + (k * 4))
  ≡ ((1 + n) * 4) + ((k * 4) + 1)
  ≡ (((1 + n) * 4) + (k * 4)) + 1
  ≡ ((1 + n + k) * 4) + 1
-}
