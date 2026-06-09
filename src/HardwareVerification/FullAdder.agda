module HardwareVerification.FullAdder where



open import HardwareVerification.Bit using (Bit; low; high)
open import HardwareVerification.XorGate using (_⊕_; xor-comm; xor-assoc; xor-fixed-high)
open import HardwareVerification.AndGate using (_∧_; and-comm)
open import HardwareVerification.OrGate using (_∨_; or-identityʳ; distrib-∨∧; or-contradiction; or-comm)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.NotGate using (¬)



FA : (A B Cᵢₙ : Bit) → (Bit × Bit)
FA A B Cᵢₙ = ⟨ Cₒᵤₜ , Sum ⟩
             where
             a⊕b = A ⊕ B
             Cₒᵤₜ = ((A ∧ B) ∨ (a⊕b ∧ Cᵢₙ))
             Sum = a⊕b ⊕ Cᵢₙ



--truth table conformance
_ : FA low low low ≡ ⟨ low , low ⟩
_ = refl

_ : FA low low high ≡ ⟨ low , high ⟩
_ = refl

_ : FA low high low ≡ ⟨ low , high ⟩
_ = refl

_ : FA low high high ≡ ⟨ high , low ⟩
_ = refl

_ : FA high low low ≡ ⟨ low , high ⟩
_ = refl

_ : FA high low high ≡ ⟨ high , low ⟩
_ = refl

_ : FA high high low ≡ ⟨ high , low ⟩
_ = refl

_ : FA high high high ≡ ⟨ high , high ⟩
_ = refl



toℕ : Bit → ℕ
toℕ low = zero
toℕ high = suc zero



FA-mathematical-conformance : (A B Cᵢₙ : Bit)
                            → let ⟨ Cₒᵤₜ , Sum ⟩ = (FA A B Cᵢₙ)
                              in toℕ A + toℕ B + toℕ Cᵢₙ ≡ (2 * toℕ Cₒᵤₜ) + toℕ Sum
FA-mathematical-conformance low low low = refl
FA-mathematical-conformance low low high = refl
FA-mathematical-conformance low high low = refl
FA-mathematical-conformance low high high = refl
FA-mathematical-conformance high low low = refl
FA-mathematical-conformance high low high = refl
FA-mathematical-conformance high high low = refl
FA-mathematical-conformance high high high = refl



--Cₒᵤₜ is equivalent to the majority function, in this case, at least two of the three inputs must be high
FA-majority : (A B Cᵢₙ : Bit)
            → let ⟨ Cₒᵤₜ , Sum ⟩ = (FA A B Cᵢₙ)
              in Cₒᵤₜ ≡ ((A ∧ B) ∨ (B ∧ Cᵢₙ) ∨ (Cᵢₙ ∧ A))
FA-majority low low low = refl
FA-majority low low high = refl
FA-majority low high low = refl
FA-majority low high high = refl
FA-majority high low low = refl
FA-majority high low high = refl
FA-majority high high low = refl
FA-majority high high high = refl



--bit flip duality: inverted inputs gives inverted outputs, this is a key property of symmetric boolean functions
FA-dual : (A B Cᵢₙ : Bit)
        → let ⟨ Cₒᵤₜ , Sum ⟩ = (FA A B Cᵢₙ)
          in (FA (¬ A) (¬ B) (¬ Cᵢₙ)) ≡ ⟨ ¬ Cₒᵤₜ , ¬ Sum ⟩
FA-dual low low low = refl
FA-dual low low high = refl
FA-dual low high low = refl
FA-dual low high high = refl
FA-dual high low low = refl
FA-dual high low high = refl
FA-dual high high low = refl
FA-dual high high high = refl



--total symmetry: FA behaves identically even with permuted inputs, that is, order of inputs doesn't matter
FA-permute₁ : (A B Cᵢₙ : Bit) → FA A B Cᵢₙ ≡ FA B A Cᵢₙ
FA-permute₁ A B Cᵢₙ =
  begin
    FA A B Cᵢₙ
  ≡⟨⟩
    ⟨ (A ∧ B) ∨ ((A ⊕ B) ∧ Cᵢₙ) , (A ⊕ B) ⊕ Cᵢₙ ⟩
  ≡⟨ cong₂ (λ x y → ⟨ x , y ⟩) (cong₂ (λ p q → p ∨ (q ∧ Cᵢₙ)) (and-comm A B) (xor-comm A B)) (cong (_⊕ Cᵢₙ) (xor-comm A B)) ⟩
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
    lemma-carry low b c rewrite and-comm b c = refl
    lemma-carry high b c rewrite or-identityʳ (¬ b)
                               | or-identityʳ (¬ c)
                               | distrib-∨∧ b (¬ b) c
                               | distrib-∨∧ c (¬ c) b
                               | or-contradiction b
                               | or-contradiction c
                               | or-comm b c
                               = refl
    --
    lemma-sum : ∀ a b c → (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
    lemma-sum a b c rewrite sym (xor-assoc a b c)
                          | xor-comm b c
                          | xor-assoc a c b
                          = refl
