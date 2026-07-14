module Naturals.Properties.Divisibility2 where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_)
open import Divisibility.RuleB using (Div; dz; ds; da→d[a*b]; da→db→d[a+b]; da→d[a+b]→db)
open import Relation.Nullary using (¬_)
open import Utilities using (_²)
open import Polynomials.Binomials using ([a+b]²≡a²+2ab+b²)
open import Relation.Binary.PropositionalEquality using (subst)



Div2 = Div 2 (s≤s z≤n)



even-n→odd-sn : ∀ {n : ℕ} → Div2 n → ¬ Div2 (suc n)
even-n→odd-sn dz ()
even-n→odd-sn (ds d2-n) (ds d2-sn) = even-n→odd-sn d2-n d2-sn



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
d2-n²→d2-n (suc (suc n)) d2-sn² = d2-n→d2-ssn n (d2-n²→d2-n n (d2-4+4n+n²→d2-n² n (d2-ssn²-expansion n d2-sn²)))
