module HardwareVerification.Word where



open import Data.Vec using (Vec; []; _∷_)
open import HardwareVerification.Bit using (Bit; O; I; valB)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (*-assoc; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning



--The following uses LSB at the leftmost position (head)
Word = Vec Bit



--semantics or mathematical meaning of Word with LSB on the left
--pv is the place value in a positional base 2 number system
valW-calc : {n : ℕ} → (k pv : ℕ) → pv ≡ 2 ^ k → Word n → ℕ
valW-calc {zero} k pv pow2 [] = 0
valW-calc {suc n} k pv pow2 (w ∷ W) = (pv * (valB w)) + valW-calc (suc k) (2 * pv) (cong (2 *_) pow2) W

valW : {n : ℕ} → Word n → ℕ
valW W = valW-calc 0 1 refl W



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
