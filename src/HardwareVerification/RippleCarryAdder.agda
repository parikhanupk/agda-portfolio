module HardwareVerification.RippleCarryAdder where



open import Data.Vec using (Vec; []; _∷_)
open import HardwareVerification.Bit using (Bit; O; I; valB)
open import HardwareVerification.FullAdder using (FA; FA-valid)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc; *-assoc; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)



--The following uses LSB at the leftmost position (head)
Word = Vec Bit

--semantics or mathematical meaning of Word with LSB on the left
--pv is the place value in a positional base 2 number system
valc : {n : ℕ} → (k pv : ℕ) → pv ≡ 2 ^ k → Word n → ℕ
valc {zero} k pv pow2  [] = 0
valc {suc n} k pv pow2 (w ∷ W) = (pv * (valB w)) + valc (suc k) (2 * pv) (cong (2 *_) pow2) W

valW : {n : ℕ} → Word n → ℕ
valW W = valc 0 1 refl W



RCA : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit) → (Bit × Word n)
RCA [] [] Cᵢₙ = ⟨ Cᵢₙ , [] ⟩
RCA (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in ⟨ cᵣ , (s₀ ∷ sᵣ) ⟩

--semantics or mathematical meaning
valRCA : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit) → ℕ
valRCA {n} A B Cᵢₙ = let ⟨ Cₒᵤₜ , Sum ⟩ = RCA A B Cᵢₙ
                     in ((2 ^ n) * (valB Cₒᵤₜ)) + valW Sum



A = O ∷ I ∷ I ∷ []
B = I ∷ O ∷ I ∷ []
Cᵢₙ = O

_ : valW A ≡ 6
_ = refl

_ : valW B ≡ 5
_ = refl

_ : RCA A B Cᵢₙ ≡ ⟨ I , I ∷ I ∷ O ∷ [] ⟩
_ = refl

_ : valW A + valW B + valB Cᵢₙ ≡ valRCA A B Cᵢₙ
_ = refl



lemma-pv : ∀ {n : ℕ} → (k pv : ℕ) → (pow2 : pv ≡ 2 ^ k) → (W : Word n)
         → 2 * (valc k pv pow2 W) ≡ valc (suc k) (2 * pv) (cong (2 *_) pow2) W
lemma-pv {zero} k pv pow2 [] = refl
lemma-pv {suc n} k pv pow2 (w ∷ W) =
  begin
    2 * valc k pv pow2 (w ∷ W)
  ≡⟨ refl ⟩
    2 * ((pv * (valB w)) + valc (suc k) (2 * pv) (cong (2 *_) pow2) W)
  ≡⟨ *-distribˡ-+ 2 (pv * (valB w)) (valc (suc k) (2 * pv) (cong (_*_ 2) pow2) W) ⟩
    (2 * (pv * (valB w))) + (2 * (valc (suc k) (2 * pv) (cong (2 *_) pow2) W))
  ≡⟨ cong (_+ (2 * (valc (suc k) (2 * pv) (cong (2 *_) pow2) W))) (sym (*-assoc 2 pv (valB w))) ⟩
    ((2 * pv) * (valB w)) + (2 * (valc (suc k) (2 * pv) (cong (2 *_) pow2) W))
  ≡⟨ cong (λ x → ((2 * pv) * (valB w)) + (2 * x)) (sym (lemma-pv k pv pow2 W)) ⟩
    ((2 * pv) * (valB w)) + (2 * (2 * (valc k pv pow2 W)))
  ≡⟨ cong (λ x → ((2 * pv) * (valB w)) + (2 * x)) (lemma-pv k pv pow2 W) ⟩
    ((2 * pv) * (valB w)) + 2 * (valc (suc k) (2 * pv) (cong (λ x → 2 * x) pow2) W)
  ≡⟨ cong (((2 * pv) * (valB w)) +_) (lemma-pv (suc k) (2 * pv) (cong (λ x → 2 * x) pow2) W) ⟩
    ((2 * pv) * (valB w)) + valc (suc (suc k)) (2 * (2 * pv)) (cong (λ x → 2 * (2 * x)) pow2) W
  ≡⟨ refl ⟩
    valc (suc k) (2 * pv) (cong (_*_ 2) pow2) (w ∷ W)
  ∎



a+[b+c]≡b+[a+c] : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
a+[b+c]≡b+[a+c] a b c rewrite sym (+-assoc a b c)
                            | +-comm a b
                            | +-assoc b a c
                            = refl



[a+b]+[c+d]≡[c+a]+[d+b] : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (c + a) + (d + b)
[a+b]+[c+d]≡[c+a]+[d+b] a b c d rewrite sym (+-assoc (a + b) c d)
                                      | +-comm (a + b) c
                                      | sym (+-assoc c a b)
                                      | +-assoc (c + a) b d
                                      | +-comm b d
                                      = refl



RCA-valid : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
          → valRCA A B Cᵢₙ ≡ valW A + valW B + valB Cᵢₙ
RCA-valid {zero} [] [] Cᵢₙ rewrite +-identityʳ (valB Cᵢₙ)
                                 | +-identityʳ (valB Cᵢₙ)
                                 = refl
RCA-valid {suc n} (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in
  begin
    valRCA (a ∷ A) (b ∷ B) Cᵢₙ
  ≡⟨ refl ⟩
    ((2 ^ suc n) * valB cᵣ) + (valW (s₀ ∷ sᵣ))
  ≡⟨ refl ⟩
    ((2 ^ suc n) * valB cᵣ) + ((1 * (valB s₀)) + valc 1 2 refl sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + (x + valc 1 2 refl sᵣ)) (+-identityʳ (valB s₀)) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + valc 1 2 refl sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + x)) (sym (lemma-pv 0 1 refl sᵣ)) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + 2 * (valc 0 1 refl sᵣ))
  ≡⟨ a+[b+c]≡b+[a+c] ((2 ^ suc n) * valB cᵣ) (valB s₀) (2 * valc 0 1 refl sᵣ) ⟩
    (valB s₀) + (((2 ^ suc n) * valB cᵣ) + (2 * (valc 0 1 refl sᵣ)))
  ≡⟨ refl ⟩
    (valB s₀) + (((2 * (2 ^ n)) * valB cᵣ) + (2 * (valc 0 1 refl sᵣ)))
  ≡⟨ cong (λ x → (valB s₀) + (x + (2 * (valc 0 1 refl sᵣ)))) (*-assoc 2 (2 ^ n) (valB cᵣ)) ⟩
    (valB s₀) + ((2 * ((2 ^ n) * valB cᵣ)) + (2 * (valc 0 1 refl sᵣ)))
  ≡⟨ cong (λ x → (valB s₀) + x) (sym (*-distribˡ-+ 2 ((2 ^ n) * valB cᵣ) (valc 0 1 refl sᵣ))) ⟩
    (valB s₀) + 2 * (((2 ^ n) * valB cᵣ) + (valc 0 1 refl sᵣ))
  ≡⟨ cong (λ x → (valB s₀) + 2 * x) (RCA-valid A B c₀) ⟩
    (valB s₀) + 2 * ((valW A) + (valW B) + valB c₀)
  ≡⟨ cong (λ x → (valB s₀) + x) (*-distribˡ-+ 2 (valW A + valW B) (valB c₀)) ⟩
    (valB s₀) + (2 * ((valW A) + (valW B)) + 2 * (valB c₀))
  ≡⟨ a+[b+c]≡b+[a+c] (valB s₀) (2 * ((valW A) + (valW B))) (2 * valB c₀) ⟩
    (2 * ((valW A) + (valW B))) + ((valB s₀) + (2 * (valB c₀)))
  ≡⟨ cong (λ x → (2 * ((valW A) + (valW B))) + x) (+-comm (valB s₀) (2 * valB c₀)) ⟩
    (2 * ((valW A) + (valW B))) + ((2 * (valB c₀)) + (valB s₀))
  ≡⟨ cong (λ x → (2 * ((valW A) + (valW B))) + x) (FA-valid a b Cᵢₙ) ⟩
    (2 * ((valW A) + (valW B))) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ cong₂ (λ x y → x + y) (*-distribˡ-+ 2 (valW A) (valW B)) refl ⟩
    (2 * (valW A) + 2 * (valW B)) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ cong₂ (λ x y → x + y + (valB a + valB b + valB Cᵢₙ))
           (lemma-pv 0 1 refl A)
           (lemma-pv 0 1 refl B) ⟩
    ((valc 1 2 refl A) + (valc 1 2 refl B)) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ sym (+-assoc ((valc 1 2 refl A) + (valc 1 2 refl B)) (valB a + valB b) (valB Cᵢₙ)) ⟩
    ((valc 1 2 refl A) + (valc 1 2 refl B)) + (valB a + valB b) + valB Cᵢₙ
  ≡⟨ cong (_+ valB Cᵢₙ) ([a+b]+[c+d]≡[c+a]+[d+b] (valc 1 2 refl A) (valc 1 2 refl B) (valB a) (valB b)) ⟩
    (valB a + (valc 1 2 refl A)) + (valB b + (valc 1 2 refl B)) + valB Cᵢₙ
  ≡⟨ cong₂ (λ x y → (x + (valc 1 2 refl A)) + (y + valc 1 2 refl B) + valB Cᵢₙ)
           (sym (+-identityʳ (valB a)))
           (sym (+-identityʳ (valB b))) ⟩
    valW (a ∷ A) + valW (b ∷ B) + valB Cᵢₙ
  ∎
