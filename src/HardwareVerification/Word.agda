module HardwareVerification.Word where



open import Data.Vec using (Vec; []; _∷_)
open import HardwareVerification.Bit using (Bit; O; I; valB)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z≤n; s≤s; _%_; _/_; _>_; _∸_)
open import Data.Nat.Properties using (*-assoc; *-distribˡ-+; +-comm; +-identityʳ; *-distribˡ-∸)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.DivMod using (m/n<m; m%n<n; +-distrib-/-∣ˡ)
open import Data.Nat.Divisibility using (∣-refl)
open import Utilities using (a+[b∸c]≡b∸[c∸a]; a≤aˢⁿ)



--The following uses LSB at the leftmost position (head)
Word = Vec Bit



--semantics or mathematical meaning of Word with LSB on the left
--pv is the place value in a positional base 2 number system
valW-calc : {n : ℕ} → (k pv : ℕ) → pv ≡ 2 ^ k → Word n → ℕ
valW-calc {zero} k pv pow2 [] = 0
valW-calc {suc n} k pv pow2 (w ∷ W) = (pv * (valB w)) + valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W

valW : {n : ℕ} → Word n → ℕ
valW W = valW-calc 0 1 refl W



0<ab : ∀ (a b : ℕ) → a > 0 → b > 0 → 0 < a * b
0<ab (suc a) (suc b) sa>0 sb>0 = s≤s z≤n

0<aᵇ : ∀ (a b : ℕ) → a > 0 → 0 < a ^ b
0<aᵇ (suc a) zero sa>0 = s≤s z≤n
0<aᵇ (suc a) (suc b) sa>0 = 0<ab (suc a) (suc a ^ b) (s≤s z≤n) (0<aᵇ (suc a) b (s≤s z≤n))

2sa≡2+2a : ∀ (a : ℕ) → 2 * (suc a) ≡ 2 + (2 * a)
2sa≡2+2a a rewrite +-identityʳ a
                 | +-comm a (suc a)
                 = refl

[2+a]/2≡1+[a/2] : ∀ (a : ℕ) → suc (suc a) / 2 ≡ suc (a / 2)
[2+a]/2≡1+[a/2] a = +-distrib-/-∣ˡ {2} a {2} ∣-refl

a<b→b≡c→a<c : ∀ (a b c : ℕ) → a < b → b ≡ c → a < c
a<b→b≡c→a<c a b _ a<b refl = a<b

sa≤sb→a≤b : ∀ (a b : ℕ) → suc a ≤ suc b → a ≤ b
sa≤sb→a≤b a b (s≤s a≤b) = a≤b

lemma-a<2b : ∀ (a b : ℕ) → suc (suc a) < 2 * suc b → a < 2 * b
lemma-a<2b a b ssa<2sb = sa≤sb→a≤b (suc a)
                                   (2 * b)
                                   (sa≤sb→a≤b (suc (suc a))
                                              (suc (2 * b))
                                              (subst (_<_ (suc (suc a))) (2sa≡2+2a b) ssa<2sb))

lemma-ssa/2<sb : ∀ (a b : ℕ)
               → (a < 2 * b → a / 2 < b)
               → suc (suc a) < 2 * suc b
               → suc (suc a) / 2 < suc b
lemma-ssa/2<sb a b a<2b→a/2<b ssa<2sb = subst (_< suc b)
                                              (sym ([2+a]/2≡1+[a/2] a))
                                              (s≤s (a<2b→a/2<b (lemma-a<2b a b ssa<2sb)))

a<2b→a/2<b : ∀ (a b : ℕ) → a < 2 * b → a / 2 < b
a<2b→a/2<b a zero ()
a<2b→a/2<b zero (suc b) (s≤s _) = s≤s z≤n
a<2b→a/2<b (suc zero) (suc b) (s≤s _) = s≤s z≤n
a<2b→a/2<b (suc (suc a)) (suc b) ssa<2sb = lemma-ssa/2<sb a b (a<2b→a/2<b a b) ssa<2sb

v<2ˢⁿ→v/2<2ⁿ : ∀ (v n : ℕ) → v < 2 ^ (suc n) → v / 2 < 2 ^ n
v<2ˢⁿ→v/2<2ⁿ v n v<2ˢⁿ = a<2b→a/2<b v (2 ^ n) v<2ˢⁿ

v%2≡0|1 : ∀ (v : ℕ) → (v % 2 ≡ 0) ⊎ (v % 2 ≡ 1)
v%2≡0|1 zero = inj₁ refl
v%2≡0|1 (suc zero) = inj₂ refl
v%2≡0|1 (suc (suc v)) = v%2≡0|1 v

fromℕ : {n : ℕ} → (v : ℕ) → v < 2 ^ n → Word n
fromℕ {zero} zero (s≤s z≤n) = []
fromℕ {suc n} v v<2ˢⁿ with v%2≡0|1 v
... | inj₁ v%2≡0 = O ∷ fromℕ (v / 2) (v<2ˢⁿ→v/2<2ⁿ v n v<2ˢⁿ)
... | inj₂ v%2≡1 = I ∷ fromℕ (v / 2) (v<2ˢⁿ→v/2<2ⁿ v n v<2ˢⁿ)



lemma-pv : ∀ {n : ℕ} → (k pv : ℕ) → (pow2 : pv ≡ 2 ^ k) → (W : Word n)
         → 2 * (valW-calc k pv pow2 W) ≡ valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W
lemma-pv {zero} k pv pow2 [] = refl
lemma-pv {suc n} k pv pow2 (w ∷ W) =
  begin
    2 * valW-calc k pv pow2 (w ∷ W)
  ≡⟨ refl ⟩
    2 * ((pv * (valB w)) + valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W)
  ≡⟨ *-distribˡ-+ 2 (pv * (valB w)) (valW-calc (suc k) (2 * pv) (cong (_*_ 2) pow2) W) ⟩
    (2 * (pv * (valB w))) + (2 * (valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W))
  ≡⟨ cong (_+ (2 * (valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W))) (sym (*-assoc 2 pv (valB w))) ⟩
    ((2 * pv) * (valB w)) + (2 * (valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W))
  ≡⟨ cong (λ x → ((2 * pv) * (valB w)) + (2 * x)) (sym (lemma-pv k pv pow2 W)) ⟩
    ((2 * pv) * (valB w)) + (2 * (2 * (valW-calc k pv pow2 W)))
  ≡⟨ cong (λ x → ((2 * pv) * (valB w)) + (2 * x)) (lemma-pv k pv pow2 W) ⟩
    ((2 * pv) * (valB w)) + 2 * (valW-calc (suc k) (2 * pv) (cong (λ x → 2 * x) pow2) W)
  ≡⟨ cong (((2 * pv) * (valB w)) +_) (lemma-pv (suc k) (2 * pv) (cong (λ x → 2 * x) pow2) W) ⟩
    ((2 * pv) * (valB w)) + valW-calc (suc (suc k)) (2 * (2 * pv)) (cong (λ x → 2 * (2 * x)) pow2) W
  ≡⟨ refl ⟩
    valW-calc (suc k) (2 * pv) (cong (_*_ 2) pow2) (w ∷ W)
  ∎



wordZeros : (n : ℕ) → Word n
wordZeros zero = []
wordZeros (suc n) = O ∷ wordZeros n



wordOnes : (n : ℕ) → Word n
wordOnes zero = []
wordOnes (suc n) = I ∷ (wordOnes n)



valW[wordZeros]≡0 : ∀ (n : ℕ) → valW (wordZeros n) ≡ 0
valW[wordZeros]≡0 zero = refl
valW[wordZeros]≡0 (suc n) =
  begin
    valW (wordZeros (suc n))
  ≡⟨ refl ⟩
    valW (O ∷ wordZeros n)
  ≡⟨ refl ⟩
    valW-calc 0 1 refl (O ∷ wordZeros n)
  ≡⟨ refl ⟩
    valW-calc 1 2 refl (wordZeros n)
  ≡⟨ sym (lemma-pv 0 1 refl (wordZeros n)) ⟩
    2 * (valW-calc 0 1 refl (wordZeros n))
  ≡⟨ refl ⟩
    2 * valW (wordZeros n)
  ≡⟨ cong (2 *_) (valW[wordZeros]≡0 n) ⟩
    0
  ∎



valW[wordOnes]≡2ⁿ∸1 : ∀ (n : ℕ) → valW (wordOnes n) ≡ 2 ^ n ∸ 1
valW[wordOnes]≡2ⁿ∸1 zero = refl
valW[wordOnes]≡2ⁿ∸1 (suc n) =
  begin
    valW (wordOnes (suc n))
  ≡⟨ refl ⟩
    valW (I ∷ wordOnes n)
  ≡⟨ refl ⟩
    valW-calc 0 1 refl (I ∷ wordOnes n)
  ≡⟨ refl ⟩
    1 + (valW-calc 1 2 refl (wordOnes n))
  ≡⟨ cong (1 +_) (sym (lemma-pv 0 1 refl (wordOnes n))) ⟩
    1 + 2 * (valW-calc 0 1 refl (wordOnes n))
  ≡⟨ refl ⟩
    1 + 2 * (valW (wordOnes n))
  ≡⟨ cong (λ x → 1 + 2 * x) (valW[wordOnes]≡2ⁿ∸1 n) ⟩
    1 + 2 * (2 ^ n ∸ 1)
  ≡⟨ cong (1 +_) (*-distribˡ-∸ 2 (2 ^ n) 1) ⟩
    1 + ((2 * 2 ^ n) ∸ (2 * 1))
  ≡⟨ refl ⟩
    1 + ((2 ^ suc n) ∸ 2)
  ≡⟨ a+[b∸c]≡b∸[c∸a] 1 (2 ^ (suc n)) 2 (s≤s z≤n) (a≤aˢⁿ 2 n) ⟩
    (2 ^ suc n) ∸ (2 ∸ 1)
  ≡⟨ refl ⟩
    2 ^ suc n ∸ 1
  ∎
