module HardwareVerification.RippleCarryAdder where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _/_; _%_; >-nonZero; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; *-assoc; *-distribˡ-+)
open import HardwareVerification.Bit using (Bit; O; I; valB)
open import HardwareVerification.Word using (Word; valW; valW-calc; lemma-pv; wordZeros)
open import Data.Vec using ([]; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import HardwareVerification.FullAdder using (FA; FA-valid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Divisibility.RuleB using (b≥1→bᵃ≥1)



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
    ((2 ^ suc n) * valB cᵣ) + ((1 * (valB s₀)) + valW-calc 1 2 refl sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + (x + valW-calc 1 2 refl sᵣ)) (+-identityʳ (valB s₀)) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + valW-calc 1 2 refl sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + x)) (sym (lemma-pv 0 1 refl sᵣ)) ⟩
    ((2 ^ suc n) * valB cᵣ) + ((valB s₀) + 2 * (valW-calc 0 1 refl sᵣ))
  ≡⟨ a+[b+c]≡b+[a+c] ((2 ^ suc n) * valB cᵣ) (valB s₀) (2 * valW-calc 0 1 refl sᵣ) ⟩
    (valB s₀) + (((2 ^ suc n) * valB cᵣ) + (2 * (valW-calc 0 1 refl sᵣ)))
  ≡⟨ refl ⟩
    (valB s₀) + (((2 * (2 ^ n)) * valB cᵣ) + (2 * (valW-calc 0 1 refl sᵣ)))
  ≡⟨ cong (λ x → (valB s₀) + (x + (2 * (valW-calc 0 1 refl sᵣ)))) (*-assoc 2 (2 ^ n) (valB cᵣ)) ⟩
    (valB s₀) + ((2 * ((2 ^ n) * valB cᵣ)) + (2 * (valW-calc 0 1 refl sᵣ)))
  ≡⟨ cong (λ x → (valB s₀) + x) (sym (*-distribˡ-+ 2 ((2 ^ n) * valB cᵣ) (valW-calc 0 1 refl sᵣ))) ⟩
    (valB s₀) + 2 * (((2 ^ n) * valB cᵣ) + (valW-calc 0 1 refl sᵣ))
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
    ((valW-calc 1 2 refl A) + (valW-calc 1 2 refl B)) + (valB a + valB b + valB Cᵢₙ)
  ≡⟨ sym (+-assoc ((valW-calc 1 2 refl A) + (valW-calc 1 2 refl B)) (valB a + valB b) (valB Cᵢₙ)) ⟩
    ((valW-calc 1 2 refl A) + (valW-calc 1 2 refl B)) + (valB a + valB b) + valB Cᵢₙ
  ≡⟨ cong (_+ valB Cᵢₙ) ([a+b]+[c+d]≡[c+a]+[d+b] (valW-calc 1 2 refl A) (valW-calc 1 2 refl B) (valB a) (valB b)) ⟩
    (valB a + (valW-calc 1 2 refl A)) + (valB b + (valW-calc 1 2 refl B)) + valB Cᵢₙ
  ≡⟨ cong₂ (λ x y → (x + (valW-calc 1 2 refl A)) + (y + valW-calc 1 2 refl B) + valB Cᵢₙ)
           (sym (+-identityʳ (valB a)))
           (sym (+-identityʳ (valB b))) ⟩
    valW (a ∷ A) + valW (b ∷ B) + valB Cᵢₙ
  ∎



{-
bit-div-one : ∀ (b : Bit) → (valB b) / 1 ≡ (valB b)
bit-div-one O = refl
bit-div-one I = refl

bit-mod-one : ∀ (b : Bit) → (valB b) % 1 ≡ 0
bit-mod-one O = refl
bit-mod-one I = refl

lemma-carry : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
            → let ⟨ Cₒᵤₜ , Sum ⟩ = RCA A B Cᵢₙ
                  value = valW A + valW B + valB Cᵢₙ
                  2ⁿ≢0 = >-nonZero (b≥1→bᵃ≥1 2 n (s≤s z≤n))
              in (valB Cₒᵤₜ) ≡ (value / (2 ^ n)) {{ 2ⁿ≢0 }}
lemma-carry {zero} [] [] Cᵢₙ = sym (bit-div-one Cᵢₙ)
lemma-carry {suc n} (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
      value = valW (a ∷ A) + valW (b ∷ B) + valB Cᵢₙ
      2ˢⁿ≢0 = >-nonZero (b≥1→bᵃ≥1 2 (suc n) (s≤s z≤n))
  in
  begin
    valB cᵣ
  ≡⟨ refl ⟩
    valB (proj₁ (RCA A B c₀))
  ≡⟨ refl ⟩
    valB (proj₁ (RCA A B (proj₁ (FA a b Cᵢₙ))))
  ≡⟨ {!!} ⟩
    (value / (2 ^ (suc n))) {{ 2ˢⁿ≢0 }}
  ∎

lemma-sum : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
          → let ⟨ Cₒᵤₜ , Sum ⟩ = RCA A B Cᵢₙ
                value = valW A + valW B + valB Cᵢₙ
                2ⁿ≢0 = >-nonZero (b≥1→bᵃ≥1 2 n (s≤s z≤n))
            in (valW Sum) ≡ (value % (2 ^ n)) {{ 2ⁿ≢0 }}
lemma-sum {zero} [] [] Cᵢₙ = sym (bit-mod-one Cᵢₙ)
lemma-sum {suc n} (a ∷ A) (b ∷ B) Cᵢₙ = {!!}

RCA-valid-mod : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
              → let ⟨ Cₒᵤₜ , Sum ⟩ = RCA A B Cᵢₙ
                    value = valW A + valW B + valB Cᵢₙ
                    2ⁿ≢0 = >-nonZero (b≥1→bᵃ≥1 2 n (s≤s z≤n))
                in ((valB Cₒᵤₜ) ≡ (value / (2 ^ n)) {{ 2ⁿ≢0 }} × ((valW Sum) ≡ (value % (2 ^ n)) {{ 2ⁿ≢0 }}))
RCA-valid-mod A B Cᵢₙ = ⟨ lemma-carry A B Cᵢₙ , lemma-sum A B Cᵢₙ ⟩
-}
