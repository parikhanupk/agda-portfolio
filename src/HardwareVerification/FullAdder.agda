module HardwareVerification.FullAdder where



open import HardwareVerification.Bit using (Bit; O; I; valB)
open import HardwareVerification.NotGate using (¬)
open import HardwareVerification.AndGate using (_∧_; ∧-comm; ∧-identityʳ)
open import HardwareVerification.OrGate using (_∨_; ∨-comm; b∨¬b≡I; ∨-identityʳ; distrib-∨∧)
open import HardwareVerification.XorGate using (_⊕_; ⊕-comm; b⊕I≡¬b; b⊕O≡b; ⊕-assoc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning



FA : (A B Cᵢₙ : Bit) → (Bit × Bit)
FA A B Cᵢₙ = ⟨ Cₒᵤₜ , Sum ⟩
             where
             a⊕b = A ⊕ B
             Cₒᵤₜ = ((A ∧ B) ∨ (a⊕b ∧ Cᵢₙ))
             Sum = a⊕b ⊕ Cᵢₙ



--truth table conformance
_ : FA O O O ≡ ⟨ O , O ⟩
_ = refl

_ : FA O O I ≡ ⟨ O , I ⟩
_ = refl

_ : FA O I O ≡ ⟨ O , I ⟩
_ = refl

_ : FA O I I ≡ ⟨ I , O ⟩
_ = refl

_ : FA I O O ≡ ⟨ O , I ⟩
_ = refl

_ : FA I O I ≡ ⟨ I , O ⟩
_ = refl

_ : FA I I O ≡ ⟨ I , O ⟩
_ = refl

_ : FA I I I ≡ ⟨ I , I ⟩
_ = refl



valFA : ∀ (A B Cᵢₙ : Bit) → ℕ
valFA A B Cᵢₙ = let ⟨ Cₒᵤₜ , Sum ⟩ = FA A B Cᵢₙ
                in (2 * (valB Cₒᵤₜ)) + valB Sum



valFA₁≡suc[valFA₀] : ∀ (A B : Bit) → valFA A B I ≡ suc (valFA A B O)
valFA₁≡suc[valFA₀] O O = refl
valFA₁≡suc[valFA₀] O I = refl
valFA₁≡suc[valFA₀] I O = refl
valFA₁≡suc[valFA₀] I I = refl



[a∧b]∨[a⊕b]≡a∨b : ∀ (a b : Bit) → (a ∧ b) ∨ (a ⊕ b) ≡ a ∨ b
[a∧b]∨[a⊕b]≡a∨b O b = refl
[a∧b]∨[a⊕b]≡a∨b I b =
  begin
    (I ∧ b) ∨ (I ⊕ b)
  ≡⟨ refl ⟩
    b ∨ (I ⊕ b)
  ≡⟨ cong (b ∨_) (⊕-comm I b) ⟩
    b ∨ (b ⊕ I)
  ≡⟨ cong (b ∨_) (b⊕I≡¬b b) ⟩
    b ∨ (¬ b)
  ≡⟨ b∨¬b≡I b ⟩
    I
  ∎



lemma-FA₀ : ∀ (A B : Bit) → FA A B O ≡ ⟨ A ∧ B , A ⊕ B ⟩
lemma-FA₀ A B =
  begin
    FA A B O
  ≡⟨ refl ⟩
    ⟨ ((A ∧ B) ∨ ((A ⊕ B) ∧ O)) , (A ⊕ B) ⊕ O ⟩
  ≡⟨ cong₂ (λ x y → ⟨ ((A ∧ B) ∨ x) , y ⟩) (∧-comm (A ⊕ B) O) (b⊕O≡b (A ⊕ B)) ⟩
    ⟨ ((A ∧ B) ∨ O) , (A ⊕ B) ⟩
  ≡⟨ cong (λ x → ⟨ x , (A ⊕ B) ⟩) (∨-comm (A ∧ B) O) ⟩
    ⟨ A ∧ B , A ⊕ B ⟩
  ∎

lemma-FA₁ : ∀ (A B : Bit) → FA A B I ≡ ⟨ A ∨ B , ¬ (A ⊕ B) ⟩
lemma-FA₁ A B =
  begin
    FA A B I
  ≡⟨ refl ⟩
    ⟨ ((A ∧ B) ∨ ((A ⊕ B) ∧ I)) , (A ⊕ B) ⊕ I ⟩
  ≡⟨ cong₂ (λ x y → ⟨ ((A ∧ B) ∨ x) , y ⟩) (∧-identityʳ (A ⊕ B)) (b⊕I≡¬b (A ⊕ B)) ⟩
    ⟨ ((A ∧ B) ∨ (A ⊕ B)) , ¬ (A ⊕ B) ⟩
  ≡⟨ cong (λ x → ⟨ x , ¬ (A ⊕ B) ⟩) ([a∧b]∨[a⊕b]≡a∨b A B) ⟩
    ⟨ A ∨ B , ¬ (A ⊕ B) ⟩
  ∎



FA-valid : (A B Cᵢₙ : Bit) → valFA A B Cᵢₙ ≡ valB A + valB B + valB Cᵢₙ
FA-valid O O O = refl
FA-valid O O I = refl
FA-valid O I O = refl
FA-valid O I I = refl
FA-valid I O O = refl
FA-valid I O I = refl
FA-valid I I O = refl
FA-valid I I I = refl



--Cₒᵤₜ is equivalent to the majority function, in this case, at least two of the three inputs must be I
FA-majority : (A B Cᵢₙ : Bit)
            → let ⟨ Cₒᵤₜ , Sum ⟩ = (FA A B Cᵢₙ)
              in Cₒᵤₜ ≡ ((A ∧ B) ∨ (B ∧ Cᵢₙ) ∨ (Cᵢₙ ∧ A))
FA-majority O O O = refl
FA-majority O O I = refl
FA-majority O I O = refl
FA-majority O I I = refl
FA-majority I O O = refl
FA-majority I O I = refl
FA-majority I I O = refl
FA-majority I I I = refl



--bit flip duality: inverted inputs gives inverted outputs, this is a key property of symmetric boolean functions
FA-dual : (A B Cᵢₙ : Bit)
        → let ⟨ Cₒᵤₜ , Sum ⟩ = (FA A B Cᵢₙ)
          in (FA (¬ A) (¬ B) (¬ Cᵢₙ)) ≡ ⟨ ¬ Cₒᵤₜ , ¬ Sum ⟩
FA-dual O O O = refl
FA-dual O O I = refl
FA-dual O I O = refl
FA-dual O I I = refl
FA-dual I O O = refl
FA-dual I O I = refl
FA-dual I I O = refl
FA-dual I I I = refl



--total symmetry: FA behaves identically even with permuted inputs, that is, order of inputs doesn't matter
FA-permute₁ : (A B Cᵢₙ : Bit) → FA A B Cᵢₙ ≡ FA B A Cᵢₙ
FA-permute₁ A B Cᵢₙ =
  begin
    FA A B Cᵢₙ
  ≡⟨⟩
    ⟨ (A ∧ B) ∨ ((A ⊕ B) ∧ Cᵢₙ) , (A ⊕ B) ⊕ Cᵢₙ ⟩
  ≡⟨ cong₂ (λ x y → ⟨ x , y ⟩) (cong₂ (λ p q → p ∨ (q ∧ Cᵢₙ)) (∧-comm A B) (⊕-comm A B)) (cong (_⊕ Cᵢₙ) (⊕-comm A B)) ⟩
    ⟨ (B ∧ A) ∨ ((B ⊕ A) ∧ Cᵢₙ) , (B ⊕ A) ⊕ Cᵢₙ ⟩
  ≡⟨⟩
    FA B A Cᵢₙ
  ∎

FA-permute₂ : (A B Cᵢₙ : Bit) → FA A B Cᵢₙ ≡ FA A Cᵢₙ B
FA-permute₂ A B Cᵢₙ =
  begin
    FA A B Cᵢₙ
  ≡⟨⟩
    ⟨ (A ∧ B) ∨ ((A ⊕ B) ∧ Cᵢₙ) , (A ⊕ B) ⊕ Cᵢₙ ⟩
  ≡⟨ cong₂ (λ x y → ⟨ x , y ⟩) (lemma-carry A B Cᵢₙ) (lemma-sum A B Cᵢₙ) ⟩
    ⟨ (A ∧ Cᵢₙ) ∨ ((A ⊕ Cᵢₙ) ∧ B) , (A ⊕ Cᵢₙ) ⊕ B ⟩
  ≡⟨⟩
    FA A Cᵢₙ B
  ∎ where
    lemma-carry : ∀ a b c → a ∧ b ∨ (a ⊕ b) ∧ c ≡ a ∧ c ∨ (a ⊕ c) ∧ b
    lemma-carry O b c rewrite ∧-comm b c = refl
    lemma-carry I b c rewrite ∨-identityʳ (¬ b)
                               | ∨-identityʳ (¬ c)
                               | distrib-∨∧ b (¬ b) c
                               | distrib-∨∧ c (¬ c) b
                               | b∨¬b≡I b
                               | b∨¬b≡I c
                               | ∨-comm b c
                               = refl
    --
    lemma-sum : ∀ a b c → (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
    lemma-sum a b c rewrite sym (⊕-assoc a b c)
                          | ⊕-comm b c
                          | ⊕-assoc a c b
                          = refl
