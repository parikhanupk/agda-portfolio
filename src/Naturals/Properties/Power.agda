module Naturals.Properties.Power where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc; *-assoc; *-distribʳ-+; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (_²; +-swap)
open import Polynomials.Binomials using ([a+b]²≡a²+2ab+b²)
open import Divisibility.RuleB using (a≤c→b≤d→a+b≤c+d)



9≤16 : 9 ≤ 16
9≤16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))



a≡a→a≤a : ∀ (a : ℕ) → a ≡ a → a ≤ a
a≡a→a≤a zero refl = z≤n
a≡a→a≤a (suc a) refl = s≤s (a≡a→a≤a a refl)



a≤b→c+a≤c+b : ∀ a b c → a ≤ b → c + a ≤ c + b
a≤b→c+a≤c+b a b zero a≤b = a≤b
a≤b→c+a≤c+b a b (suc c) a≤b = s≤s (a≤b→c+a≤c+b a b c a≤b)



a≤b→a≤sb : ∀ a b → a ≤ b → a ≤ suc b
a≤b→a≤sb zero _ _ = z≤n
a≤b→a≤sb (suc a) (suc b) (s≤s a≤b) = s≤s (a≤b→a≤sb a b a≤b)



a≤b→a≤b+c : ∀ a b c → a ≤ b → a ≤ b + c
a≤b→a≤b+c a b zero a≤b rewrite +-identityʳ b = a≤b
a≤b→a≤b+c a b (suc c) a≤b rewrite +-comm b (suc c)
                                | +-comm c b
                                = a≤b→a≤sb a (b + c) (a≤b→a≤b+c a b c a≤b)



a≤b→an≤bn : ∀ a b n → a ≤ b → a * n ≤ b * n
a≤b→an≤bn zero _ _ _ = z≤n
a≤b→an≤bn (suc a) (suc b) n (s≤s a≤b) = a≤b→c+a≤c+b (a * n) (b * n) n (a≤b→an≤bn a b n a≤b)



[a+b+n]+[c+d]≡[a+c]+[b+d]+n : ∀ a b c d n → (a + b + n) + (c + d) ≡ (a + c) + (b + d) + n
[a+b+n]+[c+d]≡[a+c]+[b+d]+n a b c d n rewrite +-swap (a + b) n (c + d)
                                            | +-swap a b (c + d)
                                            | sym (+-assoc a c d)
                                            | +-swap (a + c) d b
                                            | +-assoc (a + c) b d
                                            = refl



a+b≡c→a+b≤d→c≤d : ∀ a b c d → a + b ≡ c → a + b ≤ d → c ≤ d
a+b≡c→a+b≤d→c≤d a b c d refl a+b≤d = a+b≤d



a≤b+b→a≤2b : ∀ a b → a ≤ b + b → a ≤ 2 * b
a≤b+b→a≤2b a b a≤b+b rewrite +-identityʳ b = a≤b+b



n≥4→n²≤2ⁿ : ∀ (n : ℕ) → (4 + n) ² ≤ (2 ^ (4 + n))
n≥4→n²≤2ⁿ zero = a≡a→a≤a (4 ²) refl
n≥4→n²≤2ⁿ (suc n) = ihs-2rhs n (n≥4→n²≤2ⁿ n)
                    where
                    [16+8n+n²]+[9+2n]≡[4+sn]² : ∀ (n : ℕ)
                                              → (16 + (8 * n) + n ²) + (9 + (2 * n))
                                              ≡ (4 + (suc n)) ²
                    [16+8n+n²]+[9+2n]≡[4+sn]² n =
                      begin
                        (16 + (8 * n) + n ²) + (9 + (2 * n))
                      ≡⟨ [a+b+n]+[c+d]≡[a+c]+[b+d]+n 16 (8 * n) 9 (2 * n) (n ²) ⟩
                        25 + ((8 * n) + (2 * n)) + (n ²)
                      ≡⟨ cong (λ x → 25 + x + (n ²)) (sym (*-distribʳ-+ n 8 2)) ⟩
                        25 + ((2 * 5) * n) + (n ²)
                      ≡⟨ cong (λ x → 25 + x + (n ²)) (*-assoc 2 5 n) ⟩
                        25 + (2 * (5 * n)) + (n ²)
                      ≡⟨ sym ([a+b]²≡a²+2ab+b² 5 n) ⟩  
                        (5 + n) ²
                      ≡⟨ refl ⟩
                        (4 + suc n) ²
                      ∎
                    --
                    [4+n]²≡[16+8n+n²] : ∀ (n : ℕ) → (4 + n) ² ≡ 16 + (8 * n) + n ²
                    [4+n]²≡[16+8n+n²] n =
                      begin
                        (4 + n) ²
                      ≡⟨ [a+b]²≡a²+2ab+b² 4 n ⟩
                        16 + (2 * (4 * n)) + n ²
                      ≡⟨ cong (λ x → 16 + x + n ²) (sym (*-assoc 2 4 n)) ⟩
                        16 + ((2 * 4) * n) + n ²
                      ≡⟨ refl ⟩
                        16 + (8 * n) + n ²
                      ∎
                    --
                    [16+8n+n²]≤[4+n]² : ∀ (n : ℕ) → (16 + (8 * n) + n ²) ≤ (4 + n) ²
                    [16+8n+n²]≤[4+n]² n = subst (_≤_ (16 + (8 * n) + n ²))
                                                (sym ([4+n]²≡[16+8n+n²] n))
                                                (a≡a→a≤a (16 + (8 * n) + (n ²)) refl)
                    --
                    [9+2n]≤[16+8n] : ∀ (n : ℕ) → 9 + (2 * n) ≤ 16 + (8 * n)
                    [9+2n]≤[16+8n] n = a≤c→b≤d→a+b≤c+d 9 (2 * n) 16 (8 * n) 9≤16 (a≤b→an≤bn 2 8 n (s≤s (s≤s z≤n)))
                    --
                    [9+2n]≤[16+8n+n²] : ∀ (n : ℕ) → 9 + (2 * n) ≤ 16 + (8 * n) + n ²
                    [9+2n]≤[16+8n+n²] n = a≤b→a≤b+c (9 + (2 * n)) (16 + (8 * n)) (n ²) ([9+2n]≤[16+8n] n)
                    --
                    [9+2n]≤[4+n]² : ∀ (n : ℕ) → 9 + (2 * n) ≤ (4 + n) ²
                    [9+2n]≤[4+n]² n = ≤-trans ([9+2n]≤[16+8n+n²] n) ([16+8n+n²]≤[4+n]² n)
                    --
                    [16+8n+n²]≤[2⁴⁺ⁿ] : ∀ (n : ℕ)
                                      → (4 + n) ² ≤ (2 ^ (4 + n))
                                      → (16 + (8 * n) + n ²) ≤ (2 ^ (4 + n))
                    [16+8n+n²]≤[2⁴⁺ⁿ] n ihs = ≤-trans ([16+8n+n²]≤[4+n]² n) ihs
                    --
                    [9+2n]≤[2⁴⁺ⁿ] : ∀ (n : ℕ)
                                  → (4 + n) ² ≤ (2 ^ (4 + n))
                                  → 9 + (2 * n) ≤ (2 ^ (4 + n))
                    [9+2n]≤[2⁴⁺ⁿ] n ihs = ≤-trans ([9+2n]≤[4+n]² n) ihs
                    --
                    [16+8n+n²]+[9+2n]≤2*[2⁴⁺ⁿ] : ∀ (n : ℕ)
                                               → (4 + n) ² ≤ (2 ^ (4 + n))
                                               → (16 + (8 * n) + n ²) + (9 + (2 * n))
                                               ≤ (2 ^ (4 + n)) + (2 ^ (4 + n))
                    [16+8n+n²]+[9+2n]≤2*[2⁴⁺ⁿ] n ihs = a≤c→b≤d→a+b≤c+d (16 + (8 * n) + n ²)
                                                                       (9 + (2 * n))
                                                                       (2 ^ (4 + n))
                                                                       (2 ^ (4 + n))
                                                                       ([16+8n+n²]≤[2⁴⁺ⁿ] n ihs)
                                                                       ([9+2n]≤[2⁴⁺ⁿ] n ihs)
                    --
                    ihs-rhs+rhs : ∀ (n : ℕ)
                                  → (4 + n) ² ≤ (2 ^ (4 + n))
                                  → (4 + (suc n)) ² ≤ (2 ^ (4 + n)) + (2 ^ (4 + n))
                    ihs-rhs+rhs n ihs = a+b≡c→a+b≤d→c≤d (16 + (8 * n) + n ²)
                                                        (9 + (2 * n))
                                                        ((4 + (suc n)) ²)
                                                        (2 ^ (4 + n) + 2 ^ (4 + n))
                                                        ([16+8n+n²]+[9+2n]≡[4+sn]² n)
                                                        ([16+8n+n²]+[9+2n]≤2*[2⁴⁺ⁿ] n ihs)
                    --
                    ihs-2rhs : ∀ (n : ℕ)
                             → (4 + n) ² ≤ (2 ^ (4 + n))
                             → (4 + (suc n)) ² ≤ 2 * (2 ^ (4 + n))
                    ihs-2rhs n ihs = a≤b+b→a≤2b ((4 + suc n) ²)
                                                (2 ^ (4 + n))
                                                (ihs-rhs+rhs n ihs)
