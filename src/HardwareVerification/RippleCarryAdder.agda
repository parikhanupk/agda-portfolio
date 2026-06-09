module HardwareVerification.RippleCarryAdder where



open import Data.Vec using (Vec; []; _∷_; length)
open import HardwareVerification.Bit using (Bit; low; high)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import HardwareVerification.FullAdder using (FA)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning



--The following uses LSB at the leftmost position (head)
Word = Vec Bit



RCA : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit) → (Bit × Word n)
RCA [] [] Cᵢₙ = ⟨ Cᵢₙ , [] ⟩
RCA (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in ⟨ cᵣ , (s₀ ∷ sᵣ) ⟩



--semantics or mathematical meaning
bit→ℕ : Bit → ℕ
bit→ℕ low = 0
bit→ℕ high = 1

toℕ-calc : {n : ℕ} → (pv : ℕ) → Word n → ℕ
toℕ-calc _ [] = 0
toℕ-calc pv (b ∷ bs) = ((bit→ℕ b) * pv) + toℕ-calc (2 * pv) bs

toℕ : {n : ℕ} → Word n → ℕ
toℕ word = toℕ-calc 1 word



A = low ∷ high ∷ high ∷ []
B = high ∷ low ∷ high ∷ []
Cᵢₙ = low

_ : toℕ A ≡ 6
_ = refl

_ : toℕ B ≡ 5
_ = refl

_ : RCA A B Cᵢₙ ≡ ⟨ high , high ∷ high ∷ low ∷ [] ⟩
_ = refl

_ : let ⟨ carry , sum ⟩ = RCA A B Cᵢₙ
        result = toℕ sum + ((bit→ℕ carry) * (2 ^ (length A)))
    in
    toℕ A + toℕ B + toℕ (Cᵢₙ ∷ []) ≡ result
_ = refl



{-
rca-valid : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
                    → let ⟨ carry , sum ⟩ = RCA A B Cᵢₙ
                      in toℕ A + toℕ B + toℕ (Cᵢₙ ∷ []) ≡ toℕ sum + ((bit→ℕ carry) * (2 ^ n))
rca-valid {zero} [] [] Cᵢₙ rewrite +-identityʳ (bit→ℕ Cᵢₙ * 1) = refl
rca-valid {suc n} (a ∷ A) (b ∷ B) Cᵢₙ =
  let ⟨ c₀ , s₀ ⟩ = FA a b Cᵢₙ
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in
  begin
    toℕ (a ∷ A) + toℕ (b ∷ B) + toℕ (Cᵢₙ ∷ [])
  ≡⟨⟩
    (((bit→ℕ a) * 1) + toℕ-calc (2 * 1) A) +
    (((bit→ℕ b) * 1) + toℕ-calc (2 * 1) B) +
    (((bit→ℕ Cᵢₙ) * 1) + toℕ-calc (2 * 1) [])
  ≡⟨ {!!} ⟩
    toℕ (s₀ ∷ sᵣ) + bit→ℕ cᵣ * 2 ^ (suc n)
  ∎
-}
