module Naturals.Properties.Divisibility2 where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_; _>_; _^_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-comm)
open import Divisibility.RuleB using (Div; dz; ds; da→d[a*b]; da→db→d[a+b]; da→d[a+b]→db; ds-da→da)
open import Relation.Nullary using (¬_)
open import Utilities using (_²)
open import Polynomials.Binomials using ([a+b]²≡a²+2ab+b²)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Empty using (⊥-elim)
open import Naturals.Properties.Divisibility using (¬da→db→¬d[a+b])
open import Data.Sum using (_⊎_; inj₁; inj₂)



Div2 = Div 2 (s≤s z≤n)



even-n→odd-sn : ∀ {n : ℕ} → Div2 n → ¬ Div2 (suc n)
even-n→odd-sn dz ()
even-n→odd-sn (ds d2-n) (ds d2-sn) = even-n→odd-sn d2-n d2-sn

odd-n→even-sn : ∀ {n : ℕ} → ¬ Div2 n → Div2 (suc n)
odd-n→even-sn {zero} ¬d2-0 = ⊥-elim (¬d2-0 dz)
odd-n→even-sn {suc zero} _ = ds dz
odd-n→even-sn {suc (suc n)} ¬d2-ssn = ds (odd-n→even-sn (λ d2-n → ¬d2-ssn (ds d2-n)))

d2-ssn→d2-n : ∀ {n : ℕ} → Div2 (suc (suc n)) → Div2 n
d2-ssn→d2-n (ds d2-n) = d2-n

¬odd-sn→even-n : ∀ {n : ℕ} → ¬ Div2 (suc n) → Div2 n
¬odd-sn→even-n ¬d2-sn = d2-ssn→d2-n (odd-n→even-sn ¬d2-sn)



d2-ssn²-expansion : ∀ (n : ℕ) → Div2 (suc (suc n) ²) → Div2 (4 + (2 * (2 * n)) + n ²)
d2-ssn²-expansion n d2-ssn² = subst Div2 ([a+b]²≡a²+2ab+b² 2 n) d2-ssn²

d2-2n : ∀ (n : ℕ) → Div2 (2 * n)
d2-2n n = da→d[a*b] {2} {2} {n} (s≤s z≤n) (ds dz)

d2-4+4n : ∀ (n : ℕ) → Div2 (4 + (2 * (2 * n)))
d2-4+4n n = da→db→d[a+b] {2} {4} {2 * (2 * n)} (s≤s z≤n) (ds (ds dz)) (d2-2n (2 * n))

d2-4+4n+n²→d2-n² : ∀ (n : ℕ) → Div2 (4 + (2 * (2 * n)) + n ²) → Div2 (n ²)
d2-4+4n+n²→d2-n² n d2-4+4n+n² = da→d[a+b]→db {2} {4 + (2 * (2 * n))} {n ²} (s≤s z≤n) (d2-4+4n n) d2-4+4n+n²

d2-n→d2-ssn : ∀ (n : ℕ) → Div2 n → Div2 (suc (suc n))
d2-n→d2-ssn n d2-n = ds d2-n

d2-n²→d2-n : ∀ (n : ℕ) → Div2 (n ²) → Div2 n
d2-n²→d2-n zero _ = dz
d2-n²→d2-n (suc (suc n)) d2-ssn² = d2-n→d2-ssn n (d2-n²→d2-n n (d2-4+4n+n²→d2-n² n (d2-ssn²-expansion n d2-ssn²)))



d2-n→d2-nᵖ : ∀ (n p : ℕ) → p > 0 → Div2 n → Div2 (n ^ p)
d2-n→d2-nᵖ n (suc p) p>0 d2-n = da→d[a*b] (s≤s z≤n) d2-n

d2-+-odd-odd : ∀ (a b : ℕ) → ¬ Div2 a → ¬ Div2 b → Div2 (a + b)
d2-+-odd-odd zero b ¬d2-0 _ = ⊥-elim (¬d2-0 dz)
d2-+-odd-odd (suc a) zero _ ¬d2-0 = ⊥-elim (¬d2-0 dz)
d2-+-odd-odd (suc a) (suc b) ¬d2-a ¬d2-b
             rewrite +-comm a (suc b)
                   | +-comm b a
                   = ds (da→db→d[a+b] {2} {a} {b} (s≤s z≤n)
                                      (¬odd-sn→even-n ¬d2-a)
                                      (¬odd-sn→even-n ¬d2-b))

d2-*-odd-odd : ∀ (a b : ℕ) → ¬ Div2 a → ¬ Div2 b → ¬ Div2 (a * b)
d2-*-odd-odd zero b ¬d2-0 ¬d2-b = ¬d2-0
d2-*-odd-odd (suc a) b ¬d2-a ¬d2-b = ¬da→db→¬d[a+b] (s≤s z≤n) ¬d2-b (da→d[a*b] (s≤s z≤n) (¬odd-sn→even-n ¬d2-a))

¬d2-n→¬d2-nᵖ : ∀ (n p : ℕ) → ¬ Div2 n → ¬ Div2 (n ^ p)
¬d2-n→¬d2-nᵖ n (suc p) ¬d2-n = d2-*-odd-odd n (n ^ p) ¬d2-n (¬d2-n→¬d2-nᵖ n p ¬d2-n)

d2-even-or-odd : ∀ (n : ℕ) → Div2 n ⊎ ¬ Div2 n
d2-even-or-odd zero = inj₁ dz
d2-even-or-odd (suc n) with d2-even-or-odd n
... | inj₁ d2-n = inj₂ (even-n→odd-sn d2-n)
... | inj₂ ¬d2-n = inj₁ (odd-n→even-sn ¬d2-n)

d2-n+nᵖ : ∀ (n p : ℕ) → p > 0 → Div2 (n + (n ^ p))
d2-n+nᵖ n p p>0 with d2-even-or-odd n
... | inj₁ d2-n = da→db→d[a+b] {2} {n} {n ^ p} (s≤s z≤n) d2-n (d2-n→d2-nᵖ n p p>0 d2-n)
... | inj₂ ¬d2-n = d2-+-odd-odd n (n ^ p) ¬d2-n (¬d2-n→¬d2-nᵖ n p ¬d2-n)
