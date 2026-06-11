module HardwareVerification.RippleCarryAdder where



open import Data.Vec using (Vec; []; _∷_; length)
open import HardwareVerification.Bit using (Bit; low; high; valB)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-identityʳ; *-identityʳ; *-comm; +-assoc; +-comm; *-assoc; *-distribˡ-+)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import HardwareVerification.FullAdder using (FA; valFA; valFA₁≡suc[valFA₀]; FA-valid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.AndGate using (_∧_; and-comm; and-identityʳ)
open import HardwareVerification.OrGate using (_∨_; or-comm; or-annihilation; or-contradiction)
open import HardwareVerification.XorGate using (_⊕_; xor-comm; xor-distrib-and; xor-identityʳ; xor-fixed-high)
open import HardwareVerification.NotGate using (¬)
open import Data.Product using (∃-syntax)



--The following uses LSB at the leftmost position (head)
Word = Vec Bit

--semantics or mathematical meaning when called with pv = 1
valW : {n : ℕ} → (pv : ℕ) → Word n → ℕ
valW _ [] = 0
valW pv (b ∷ bs) = (pv * (valB b)) + valW (2 * pv) bs



RCA : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit) → (Bit × Word n)
RCA [] [] Cᵢₙ = ⟨ Cᵢₙ , [] ⟩
RCA (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in ⟨ cᵣ , (s₀ ∷ sᵣ) ⟩

--semantics or mathematical meaning
valRCA : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit) → ℕ
valRCA {n} A B Cᵢₙ = let ⟨ Cₒᵤₜ , Sum ⟩ = RCA A B Cᵢₙ
                     in ((2 ^ n) * (valB Cₒᵤₜ)) + (valW 1 Sum)



A = low ∷ high ∷ high ∷ []
B = high ∷ low ∷ high ∷ []
Cᵢₙ = low

_ : valW 1 A ≡ 6
_ = refl

_ : valW 1 B ≡ 5
_ = refl

_ : RCA A B Cᵢₙ ≡ ⟨ high , high ∷ high ∷ low ∷ [] ⟩
_ = refl

_ : valW 1 A + valW 1 B + valW 1 (Cᵢₙ ∷ []) ≡ valRCA A B Cᵢₙ
_ = refl



postulate lemma-pv : ∀ {n : ℕ} → (pv : ℕ) → (W : Word n) → valW pv W ≡ pv * valW 1 W
{-
lemma-pv : ∀ {n : ℕ} → (pv : ℕ) → (W : Word n) → valW pv W ≡ pv * valW 1 W
lemma-pv {zero} pv [] = *-comm 0 pv
lemma-pv {suc n} pv (w ∷ W) =
  begin
    valW pv (w ∷ W)
  ≡⟨ refl ⟩
    (pv * (valB w)) + valW (2 * pv) W
  ≡⟨ cong (λ x → (pv * (valB w)) + valW x W) (*-comm 2 pv) ⟩
    (pv * (valB w)) + valW (pv * 2) W
  ≡⟨ cong ((pv * (valB w)) +_) {!!} ⟩
    (pv * (valB w)) + (pv * valW 2 W)
  ≡⟨ sym (*-distribˡ-+ pv (valB w) (valW 2 W)) ⟩
    pv * ((valB w) + valW 2 W)
  ≡⟨ refl ⟩
    pv * ((valB w) + valW (2 * 1) W)
  ≡⟨ cong (λ x → pv * (x + valW (2 * 1) W)) (sym (+-identityʳ (valB w))) ⟩
    pv * ((1 * (valB w)) + valW (2 * 1) W)
  ≡⟨ refl ⟩
    pv * valW 1 (w ∷ W)
  ∎
-}



a+[b+c]≡b+[a+c] : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
a+[b+c]≡b+[a+c] a b c rewrite sym (+-assoc a b c)
                            | +-comm a b
                            | +-assoc b a c = refl



[a+b]+[c+d]≡[c+a]+[d+b] : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (c + a) + (d + b)
[a+b]+[c+d]≡[c+a]+[d+b] a b c d rewrite sym (+-assoc (a + b) c d)
                                      | +-comm (a + b) c
                                      | sym (+-assoc c a b)
                                      | +-assoc (c + a) b d
                                      | +-comm b d
                                      = refl



RCA-valid : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
          → valRCA A B Cᵢₙ ≡ valW 1 A + valW 1 B + valB Cᵢₙ
RCA-valid {zero} [] [] Cᵢₙ rewrite +-identityʳ (valB Cᵢₙ)
                                 | +-identityʳ (valB Cᵢₙ)
                                 = refl
RCA-valid {suc n} (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in
  begin
    ((2 ^ suc n) * valB cᵣ) + (valW 1 (s₀ ∷ sᵣ))
  ≡⟨ refl ⟩
    ((2 ^ suc n) * valB cᵣ) + ((1 * (valB s₀)) + valW 2 sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + (x + valW 2 sᵣ)) (+-identityʳ (valB s₀)) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + valW 2 sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + x)) (lemma-pv 2 sᵣ) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + (2 * valW 1 sᵣ))
  ≡⟨ a+[b+c]≡b+[a+c] ((2 ^ suc n) * valB cᵣ) (valB s₀) (2 * valW 1 sᵣ) ⟩
    (valB s₀) + (((2 ^ suc n) * valB cᵣ) + (2 * valW 1 sᵣ))
  ≡⟨ refl ⟩
    (valB s₀) + (((2 * (2 ^ n)) * valB cᵣ) + (2 * valW 1 sᵣ))
  ≡⟨ cong (λ x → (valB s₀) + (x + (2 * valW 1 sᵣ))) (*-assoc 2 (2 ^ n) (valB cᵣ)) ⟩
    (valB s₀) + ((2 * ((2 ^ n) * valB cᵣ)) + (2 * valW 1 sᵣ))
  ≡⟨ cong (λ x → (valB s₀) + x) (sym (*-distribˡ-+ 2 ((2 ^ n) * valB cᵣ) (valW 1 sᵣ))) ⟩
    (valB s₀) + 2 * (((2 ^ n) * valB cᵣ) + valW 1 sᵣ)
  ≡⟨ cong (λ x → (valB s₀) + 2 * x) (RCA-valid A B c₀) ⟩
    (valB s₀) + 2 * (valW 1 A + valW 1 B + valB c₀)
  ≡⟨ cong ((valB s₀) +_) (*-distribˡ-+ 2 (valW 1 A + valW 1 B) (valB c₀)) ⟩
    (valB s₀) + ((2 * (valW 1 A + valW 1 B)) + (2 * valB c₀))
  ≡⟨ a+[b+c]≡b+[a+c] (valB s₀) (2 * (valW 1 A + valW 1 B)) (2 * valB c₀) ⟩
    (2 * (valW 1 A + valW 1 B)) + ((valB s₀) + (2 * valB c₀))
  ≡⟨ cong ((2 * (valW 1 A + valW 1 B)) +_) (+-comm (valB s₀) (2 * valB c₀)) ⟩
    (2 * (valW 1 A + valW 1 B)) + ((2 * valB c₀) + (valB s₀))
  ≡⟨ cong (λ x → (2 * (valW 1 A + valW 1 B)) + x) (FA-valid a b Cᵢₙ) ⟩
    (2 * (valW 1 A + valW 1 B)) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ cong₂ (λ x y → x + y) (*-distribˡ-+ 2 (valW 1 A) (valW 1 B)) refl ⟩
    (2 * valW 1 A) + (2 * valW 1 B) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ cong₂ (λ x y → x + y + (valB a + valB b + valB Cᵢₙ)) (sym (lemma-pv 2 A)) (sym (lemma-pv 2 B)) ⟩
    (valW 2 A + valW 2 B) + ((valB a + valB b) + valB Cᵢₙ)
  ≡⟨ sym (+-assoc (valW 2 A + valW 2 B) (valB a + valB b) (valB Cᵢₙ)) ⟩
    (valW 2 A + valW 2 B) + (valB a + valB b) + valB Cᵢₙ
  ≡⟨ cong (_+ valB Cᵢₙ) ([a+b]+[c+d]≡[c+a]+[d+b] (valW 2 A) (valW 2 B) (valB a) (valB b)) ⟩
    (valB a + valW 2 A) + (valB b + valW 2 B) + valB Cᵢₙ
  ≡⟨ cong₂ (λ x y → (x + valW 2 A) + (y + valW 2 B) + valB Cᵢₙ) (sym (+-identityʳ (valB a))) (sym (+-identityʳ (valB b))) ⟩
    (1 * valB a + valW 2 A) + (1 * valB b + valW 2 B) + valB Cᵢₙ
  ≡⟨ refl ⟩
    valW 1 (a ∷ A) + valW 1 (b ∷ B) + valB Cᵢₙ
  ∎
