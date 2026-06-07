module Puzzles.nnn+11n-is-div-by-6 where



open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-assoc; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Divisibility.RuleB using (Div; dz; ds; da→db→d[a+b])
open import Polynomials.Binomials using (_²; [1+n]²≡1+2n+n²; _³; [1+n]³=1+3n+3n²+n³)



Div2 = Div 2 (s≤s z≤n)
Div3 = Div 3 (s≤s z≤n)
Div6 = Div 6 (s≤s z≤n)



d2-n+n : ∀ (n : ℕ) → Div2 (n + n)
d2-n+n zero = dz
d2-n+n (suc n) rewrite +-comm n (suc n) = ds (d2-n+n n)



d2-[n+n²] : ∀ (n : ℕ) → Div2 (n + n ²)
d2-[n+n²] zero = dz
d2-[n+n²] (suc n) rewrite [1+n]²≡1+2n+n² n
                        | +-identityʳ n
                        | +-comm n (suc (n + n + n * n))
                        | +-assoc (n + n) (n * n) n
                        | +-comm (n * n) n
                        = ds (da→db→d[a+b] (s≤s z≤n) (d2-n+n n) (d2-[n+n²] n))



n+n+n≡3n : ∀ n → n + n + n ≡ 3 * n
n+n+n≡3n n rewrite +-identityʳ n
                 | +-assoc n n n
                 = refl



d2-n→d6-3n : ∀ (n : ℕ) → Div2 n → Div6 (3 * n)
d2-n→d6-3n zero d2-0 = dz
d2-n→d6-3n (suc (suc n)) (ds d2-n) rewrite +-identityʳ n
                                         | +-comm n (suc (suc n))
                                         | +-comm n (suc (suc (suc (suc (n + n)))))
                                         = ds (subst Div6 (sym (n+n+n≡3n n)) (d2-n→d6-3n n d2-n))



3[a+b+c]≡3a+3b+3c : ∀ (a b c : ℕ) → 3 * (a + b + c) ≡ (3 * a) + (3 * b) + (3 * c)
3[a+b+c]≡3a+3b+3c a b c rewrite *-distribˡ-+ 3 (a + b) c
                              | *-distribˡ-+ 3 a b
                              = refl



12+3n+3n²-is-div-by-6 : ∀ (n : ℕ) → Div6 (12 + (3 * n) + (3 * n ²))
12+3n+3n²-is-div-by-6 n = subst Div6
                                (3[a+b+c]≡3a+3b+3c 4 n (n ²))
                                (d2-n→d6-3n (4 + n + n ²) (ds (ds (d2-[n+n²] n))))



sn³+11sn≡[12+3n+3n²]+[n³+11n] : ∀ (n : ℕ) → ((suc n) ³ + (11 * (suc n))) ≡ (12 + (3 * n) + (3 * n ²)) + (n ³ + (11 * n))
sn³+11sn≡[12+3n+3n²]+[n³+11n] n =
  begin
    (suc n ³) + (11 * (suc n))
  ≡⟨ cong (_+ (11 * (suc n))) ([1+n]³=1+3n+3n²+n³ n) ⟩
    (1 + (3 * n) + (3 * n ²) + (n ³)) + (11 * (suc n))
  ≡⟨ cong ((1 + (3 * n) + (3 * n ²) + (n ³)) +_) (*-distribˡ-+ 11 1 n) ⟩
    (1 + (3 * n) + (3 * n ²) + (n ³)) + (11 + (11 * n))
  ≡⟨ sym (+-assoc (1 + (3 * n) + (3 * n ²) + (n ³)) 11 (11 * n)) ⟩
    ((1 + (3 * n) + (3 * n ²) + (n ³)) + 11) + (11 * n)
  ≡⟨ cong (_+ (11 * n)) (+-comm (1 + (3 * n) + (3 * n ²) + (n ³)) 11) ⟩
    (11 + (1 + (3 * n) + (3 * n ²) + (n ³))) + (11 * n)
  ≡⟨⟩
    ((12 + (3 * n) + (3 * n ²)) + (n ³)) + (11 * n)
  ≡⟨ +-assoc (12 + (3 * n) + (3 * n ²)) (n ³) (11 * n) ⟩
    12 + (3 * n) + (3 * (n ²)) + ((n ³) + (11 * n))
  ∎



n³+11n-is-div-by-6 : ∀ (n : ℕ) → Div6 (n ³ + (11 * n))
n³+11n-is-div-by-6 zero = dz
n³+11n-is-div-by-6 (suc n) = subst Div6
                                   (sym (sn³+11sn≡[12+3n+3n²]+[n³+11n] n))
                                   (da→db→d[a+b] (s≤s z≤n)
                                                 (12+3n+3n²-is-div-by-6 n)
                                                 (n³+11n-is-div-by-6 n))
