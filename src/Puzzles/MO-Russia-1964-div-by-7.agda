module Puzzles.MO-Russia-1964-div-by-7 where



open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s; _>_; _^_)
open import Data.Nat.Properties using (*-distribˡ-+; *-comm; +-comm; +-assoc; *-assoc; +-∸-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Divisibility.RuleB using (Div; dz; ds; da→db→d[a+b]; db→d[a*b]; da→d[a+b]→db; da→d[a*b])
open import Utilities using (a≡b→Pb→Pa)



{-
a. find all natural numbers n such that 2ⁿ - 1 is divisible by 7
   2⁰ - 1 = 0
   2¹ - 1 = 1
   2² - 1 = 3
   2³ - 1 = 7
   2⁴ - 1 = 15
   2⁵ - 1 = 31
   2⁶ - 1 = 63
   ...
   so, it seems that ∀ p → 2³ᵖ ∸ 1 is divisible by 7
   but 2³ᵖ ∸ 1 = (2³)ᵖ ∸ 1 = 8ᵖ ∸ 1
   hence the problem changes to proving the same (∀ p → 8ᵖ ∸ 1 is divisible by 7)
   it can also be viewed as a problem of proving 2ⁿ ∸ 1 is divisible by 7 if and only if n is divisible by 3
b. prove that ∀ n, 7 can't divide 2ⁿ + 1
c. prove that ∀ n, 7 can't divide 2ⁿ
   this is not a part of the original puzzle
-}



Div7 = Div 7 (s≤s z≤n)
Div3 = Div 3 (s≤s z≤n)



ab-1≡a[b-1]+[a-1] : ∀ a b → (a > 0) → (b > 0) → (a * b) ∸ 1 ≡ a * (b ∸ 1) + (a ∸ 1)
ab-1≡a[b-1]+[a-1] (suc a) (suc b) _ _ rewrite *-distribˡ-+ a 1 b
                                            | *-comm a 1
                                            | +-comm a 0
                                            | +-comm a (a * b)
                                            | +-assoc b (a * b) a
                                            = refl



a>0→b>0→ab>0 : ∀ a b → (a > 0) → (b > 0) → a * b > 0
a>0→b>0→ab>0 (suc a) (suc b) _ _ = s≤s z≤n



8ᵖ>0 : ∀ p → 8 ^ p > 0
8ᵖ>0 zero = s≤s z≤n
8ᵖ>0 (suc p) = a>0→b>0→ab>0 8 (8 ^ p) (s≤s z≤n) (8ᵖ>0 p)



proof-a : (p : ℕ) → Div7 ((8 ^ p) ∸ 1)
proof-a zero = dz
proof-a (suc p) = a≡b→Pb→Pa Div7
                            (ab-1≡a[b-1]+[a-1] 8 (8 ^ p) (s≤s z≤n) (8ᵖ>0 p))
                            (da→db→d[a+b] {7} {8 * ((8 ^ p) ∸ 1)} {(8 ∸ 1)} (s≤s z≤n)
                                          (db→d[a*b] {7} {8} {(8 ^ p) ∸ 1} (s≤s z≤n) (proof-a p))
                                          (ds dz))



a≤b→a≤[b+c] : ∀ a b c → a ≤ b → a ≤ (b + c)
a≤b→a≤[b+c] a b c z≤n = z≤n
a≤b→a≤[b+c] a b c (s≤s x) = s≤s (a≤b→a≤[b+c] _ _ c x)



1≤2ⁿ : ∀ n → 1 ≤ 2 ^ n
1≤2ⁿ zero = s≤s z≤n
1≤2ⁿ (suc n) rewrite +-comm (2 ^ n) zero = a≤b→a≤[b+c] 1 (2 ^ n) (2 ^ n) (1≤2ⁿ n)



2ˢˢˢⁿ-1≡[7*2ⁿ]+[2ⁿ-1] : ∀ n → (2 ^ suc (suc (suc n))) ∸ 1 ≡ (7 * (2 ^ n)) + ((2 ^ n) ∸ 1)
2ˢˢˢⁿ-1≡[7*2ⁿ]+[2ⁿ-1] n =
  begin
    (2 ^ suc (suc (suc n))) ∸ 1
  ≡⟨⟩
    (2 * (2 * (2 * (2 ^ n)))) ∸ 1
  ≡⟨ cong (_∸ 1) (cong (2 *_) (sym (*-assoc 2 2 (2 ^ n)))) ⟩
    (2 * (4 * (2 ^ n))) ∸ 1
  ≡⟨ cong (_∸ 1) (sym (*-assoc 2 4 (2 ^ n))) ⟩
    (8 * (2 ^ n)) ∸ 1
  ≡⟨⟩
    ((2 ^ n) + 7 * (2 ^ n)) ∸ 1
  ≡⟨ cong (_∸ 1) (+-comm (2 ^ n) (7 * 2 ^ n)) ⟩
    ((7 * (2 ^ n)) + (2 ^ n)) ∸ 1
  ≡⟨ +-∸-assoc (7 * (2 ^ n)) (1≤2ⁿ n) ⟩
    (7 * (2 ^ n)) + ((2 ^ n) ∸ 1)
  ∎



d7[2ˢˢˢⁿ-1]→d7[[7*2ⁿ]+[2ⁿ-1]] : ∀ n → Div7 ((2 ^ suc (suc (suc n))) ∸ 1) → Div7 ((7 * (2 ^ n)) + ((2 ^ n) ∸ 1))
d7[2ˢˢˢⁿ-1]→d7[[7*2ⁿ]+[2ⁿ-1]] n div7-2ˢˢˢⁿ-1 = a≡b→Pb→Pa Div7 (sym (2ˢˢˢⁿ-1≡[7*2ⁿ]+[2ⁿ-1] n)) div7-2ˢˢˢⁿ-1



div7-2ˢˢˢⁿ-1→div7-2ⁿ-1 : ∀ n → Div7 ((2 ^ suc (suc (suc n))) ∸ 1) → Div7 ((2 ^ n) ∸ 1)
div7-2ˢˢˢⁿ-1→div7-2ⁿ-1 n div7-2ˢˢˢⁿ-1 = da→d[a+b]→db {7} {7 * (2 ^ n)} {2 ^ n ∸ 1} (s≤s z≤n)
                                                     (da→d[a*b] {7} {7} {2 ^ n} (s≤s z≤n) (ds dz))
                                                     (d7[2ˢˢˢⁿ-1]→d7[[7*2ⁿ]+[2ⁿ-1]] n div7-2ˢˢˢⁿ-1)



proof-aˡ : ∀ n → Div7 ((2 ^ n) ∸ 1) → Div3 n
proof-aˡ zero _ = dz
proof-aˡ (suc (suc (suc n))) div7-2ˢˢˢⁿ-1 = ds (proof-aˡ n (div7-2ˢˢˢⁿ-1→div7-2ⁿ-1 n div7-2ˢˢˢⁿ-1))



div7-2ⁿ-1→div7-2ˢˢˢⁿ-1 : ∀ n → Div7 ((2 ^ n) ∸ 1) → Div7 ((2 ^ suc (suc (suc n))) ∸ 1)
div7-2ⁿ-1→div7-2ˢˢˢⁿ-1 n div7-2ⁿ-1 = a≡b→Pb→Pa Div7
                                               (2ˢˢˢⁿ-1≡[7*2ⁿ]+[2ⁿ-1] n)
                                               (da→db→d[a+b] {7} {7 * (2 ^ n)} {2 ^ n ∸ 1} (s≤s z≤n)
                                                             (da→d[a*b] {7} {7} {2 ^ n} (s≤s z≤n) (ds dz))
                                                             div7-2ⁿ-1)



proof-aʳ : ∀ n → Div3 n → Div7 ((2 ^ n) ∸ 1)
proof-aʳ zero div3-zero = dz
proof-aʳ (suc (suc (suc n))) (ds div3-n) = div7-2ⁿ-1→div7-2ˢˢˢⁿ-1 n (proof-aʳ n div3-n)



2ˢˢˢⁿ+1≡[7*2ⁿ]+[2ⁿ+1] : ∀ n → (2 ^ suc (suc (suc n))) + 1 ≡ (7 * (2 ^ n)) + ((2 ^ n) + 1)
2ˢˢˢⁿ+1≡[7*2ⁿ]+[2ⁿ+1] n =
  begin
    (2 ^ suc (suc (suc n))) + 1
  ≡⟨⟩
    (2 * (2 * (2 * (2 ^ n)))) + 1
  ≡⟨ cong (_+ 1) (cong (2 *_) (sym (*-assoc 2 2 (2 ^ n)))) ⟩
    (2 * (4 * (2 ^ n))) + 1
  ≡⟨ cong (_+ 1) (sym (*-assoc 2 4 (2 ^ n))) ⟩
    (8 * (2 ^ n)) + 1
  ≡⟨⟩
    ((2 ^ n) + 7 * (2 ^ n)) + 1
  ≡⟨ cong (_+ 1) (+-comm (2 ^ n) (7 * 2 ^ n)) ⟩
    (7 * (2 ^ n)) + (2 ^ n) + 1
  ≡⟨ +-assoc (7 * 2 ^ n) (2 ^ n) 1 ⟩
    (7 * (2 ^ n)) + ((2 ^ n) + 1)
  ∎



d7[[7*2ⁿ]+[2ⁿ+1]]→d7[2ⁿ+1] : ∀ n → Div7 ((7 * (2 ^ n)) + ((2 ^ n) + 1)) → Div7 ((2 ^ n) + 1)
d7[[7*2ⁿ]+[2ⁿ+1]]→d7[2ⁿ+1] n div7-[[7*2ⁿ]+[2ⁿ+1]] =
                           da→d[a+b]→db {7} {7 * (2 ^ n)} {2 ^ n + 1} (s≤s z≤n)
                                        (da→d[a*b] {7} {7} {2 ^ n} (s≤s z≤n) (ds dz))
                                        div7-[[7*2ⁿ]+[2ⁿ+1]]



proof-b : (n : ℕ) → Div7 ((2 ^ n) + 1) → ⊥
proof-b (suc (suc (suc n))) div7-2ˢˢˢⁿ+1 =
        ⊥-elim (proof-b n (d7[[7*2ⁿ]+[2ⁿ+1]]→d7[2ⁿ+1] n (a≡b→Pb→Pa Div7 (sym (2ˢˢˢⁿ+1≡[7*2ⁿ]+[2ⁿ+1] n)) div7-2ˢˢˢⁿ+1)))



d7-[a+a]→d7-a : ∀ a → Div7 (a + a) → Div7 a
d7-[a+a]→d7-a zero _ = dz
d7-[a+a]→d7-a (suc (suc (suc (suc zero)))) (ds ())
d7-[a+a]→d7-a (suc (suc (suc (suc (suc zero))))) (ds ())
d7-[a+a]→d7-a (suc (suc (suc (suc (suc (suc zero)))))) (ds ())
d7-[a+a]→d7-a (suc (suc (suc (suc (suc (suc (suc a))))))) (ds div7-a+[7+a]) =
              ds (d7-[a+a]→d7-a a (helper-[7+a]+a a (helper-a+[7+a] a div7-a+[7+a])))
              where
              helper-a+[7+a] : ∀ a → Div7 (a + (7 + a)) → Div7 ((7 + a) + a)
              helper-a+[7+a] a d7-a+[7+a] rewrite +-comm a (7 + a) = d7-a+[7+a]
              --
              helper-[7+a]+a : ∀ a → Div7 ((7 + a) + a) → Div7 (a + a)
              helper-[7+a]+a a (ds d7-a+a) = d7-a+a



proof-c : (n : ℕ) → Div7 (2 ^ n) → ⊥
proof-c (suc n) div7-2ˢⁿ rewrite +-comm (2 ^ n) 0 = ⊥-elim (proof-c n (d7-[a+a]→d7-a (2 ^ n) div7-2ˢⁿ))
