module ScratchPad where



open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _^_)
open import Data.Nat.Properties using (+-comm)



a≤b→a≤[b+c] : ∀ a b c → a ≤ b → a ≤ (b + c)
a≤b→a≤[b+c] a b c z≤n = z≤n
a≤b→a≤[b+c] a b c (s≤s x) = s≤s (a≤b→a≤[b+c] _ _ c x)



1≤2ⁿ : ∀ n → 1 ≤ 2 ^ n
1≤2ⁿ zero = s≤s z≤n
1≤2ⁿ (suc n) rewrite +-comm (2 ^ n) zero = a≤b→a≤[b+c] 1 (2 ^ n) (2 ^ n) (1≤2ⁿ n)



{-
rca-valid : {n : ℕ} → (A B : Word n) → (Cᵢₙ : Bit)
                    → let ⟨ carry , sum ⟩ = RCA A B Cᵢₙ
                      in ((2 ^ n) * (valB carry)) + (valW 1 sum) ≡ valW 1 A + valW 1 B + valW 1 (Cᵢₙ ∷ [])
rca-valid {zero} [] [] Cᵢₙ rewrite +-identityʳ (valB Cᵢₙ) = refl
rca-valid {suc n} (a ∷ A) (b ∷ B) low =
  let ⟨ c₀ , s₀ ⟩ = FA a b low
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in
  begin
    ((2 ^ suc n) * (valB cᵣ)) + valW 1 (s₀ ∷ sᵣ)
  ≡⟨ refl ⟩
    ((2 ^ suc n) * (valB cᵣ)) + ((1 * valB s₀) + valW 2 sᵣ)
  ≡⟨ cong (λ x → ((2 ^ suc n) * (valB cᵣ)) + (x + valW 2 sᵣ)) (+-identityʳ (valB s₀)) ⟩
    ((2 ^ suc n) * (valB cᵣ)) + (valB s₀ + valW 2 sᵣ)
  ≡⟨ {!!} ⟩
    ((1 * valB a) + (valW 2 A)) + ((1 * valB b) + (valW 2 B))
  ≡⟨ refl ⟩
    valW 1 (a ∷ A) + valW 1 (b ∷ B)
  ≡⟨ sym (+-identityʳ (valW 1 (a ∷ A) + valW 1 (b ∷ B))) ⟩
    valW 1 (a ∷ A) + valW 1 (b ∷ B) + 0
  ≡⟨ refl ⟩
    valW 1 (a ∷ A) + valW 1 (b ∷ B) + valW 1 (low ∷ [])
  ∎
rca-valid {suc n} (a ∷ A) (b ∷ B) high = {!!}
-}

{-
lemma-RCA : ∀ {n : ℕ} {A B : Word n} → valRCA A B high ≡ suc (valRCA A B low)
lemma-RCA {zero} {[]} {[]} = refl
lemma-RCA {suc n} {a ∷ A} {b ∷ B} =
  let ⟨ c₀ , s₀ ⟩ = FA a b high
      ⟨ cᵣ , sᵣ ⟩ = RCA A B c₀
  in
  begin
    valRCA (a ∷ A) (b ∷ B) high
  ≡⟨ refl ⟩
    ((2 ^ (suc n)) * (valB cᵣ)) + (valW 1 (s₀ ∷ sᵣ))
  ≡⟨ {!!} ⟩
    suc (valRCA (a ∷ A) (b ∷ B) low)
  ∎
-}

{-
lemma : ∀ {n : ℕ} → (a b Cᵢₙ : Bit) → (A B : Word n)
                  → valRCA (a ∷ A) (b ∷ B) Cᵢₙ
                  ≡ (valFA a b Cᵢₙ) + (2 * valRCA A B low)
lemma {n} a b Cᵢₙ A B = {!!}
-}
