module HardwareVerification.AndGate where



open import HardwareVerification.Bit using (Bit; O; I)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.NotGate using (¬; ¬¬b≡b)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)



_∧_ : Bit → Bit → Bit
O ∧ b = O
I ∧ b = b

infixr 6 _∧_



--truth table conformance
_ : O ∧ O ≡ O
_ = refl

_ : O ∧ I ≡ O
_ = refl

_ : I ∧ O ≡ O
_ = refl

_ : I ∧ I ≡ I
_ = refl



∧-comm : ∀ (a b : Bit) → a ∧ b ≡ b ∧ a
∧-comm O O = refl
∧-comm O I = refl
∧-comm I O = refl
∧-comm I I = refl



∧-assoc : ∀ (a b c : Bit) → a ∧ (b ∧ c) ≡ (a ∧ b) ∧ c
∧-assoc O b c = refl
∧-assoc I b c = refl



--idempotence
b∧b≡b : ∀ (b : Bit) → b ∧ b ≡ b
b∧b≡b O = refl
b∧b≡b I = refl



--I ∧ b ≡ b is definitional
∧-identityˡ : ∀ (b : Bit) → I ∧ b ≡ b
∧-identityˡ b = refl

∧-identityʳ : ∀ (b : Bit) → b ∧ I ≡ b
∧-identityʳ b rewrite ∧-comm b I = refl



--annihilation, O annihilates the other input
b∧O≡O : ∀ (b : Bit) → b ∧ O ≡ O
b∧O≡O b rewrite ∧-comm b O = refl



--contradiction
b∧¬b≡O : ∀ (b : Bit) → b ∧ ¬ b ≡ O
b∧¬b≡O O = refl
b∧¬b≡O I = refl



--inverted identity
¬[b∧I]≡¬b : ∀ (b : Bit) → ¬ (b ∧ I) ≡ ¬ b
¬[b∧I]≡¬b O = refl
¬[b∧I]≡¬b I = refl



--inverted annihilation
¬[b∧O]≡I : ∀ (b : Bit) → ¬ (b ∧ O) ≡ I
¬[b∧O]≡I O = refl
¬[b∧O]≡I I = refl



--double negation compatibility
¬[¬[a∧b]]≡a∧b : ∀ (a b : Bit) → ¬ (¬ (a ∧ b)) ≡ a ∧ b
¬[¬[a∧b]]≡a∧b O b = refl
¬[¬[a∧b]]≡a∧b I b rewrite ¬¬b≡b b = refl



--inversion symmetry (if two wires are opposites their ∧ is always O)
a≢b→a∧b≡0 : ∀ a b → (a ≢ b) → (a ∧ b ≡ O)
a≢b→a∧b≡0 O b a≢b = refl
a≢b→a∧b≡0 I O a≢b = refl
a≢b→a∧b≡0 I I a≢b = ⊥-elim (a≢b refl)



--compositional stability: congruence (if sub-circuits are equivalent, ∧ preserves that equivalence)
∧-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
∧-congruence refl refl = refl

∧-congruence′ : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
∧-congruence′ {a} {b} {c} {d} a≡b c≡d =
  begin
    a ∧ c
  ≡⟨ cong (_∧ c) a≡b ⟩
    b ∧ c
  ≡⟨ cong (b ∧_) c≡d ⟩
    b ∧ d
  ∎



--compositional stability: reflexivity of ∧
∧-reflexivity : ∀ {a b} → a ≡ b → (a ∧ a) ≡ (b ∧ b)
∧-reflexivity refl = refl

∧-reflexivity′ : ∀ {a b} → a ≡ b → (a ∧ a) ≡ (b ∧ b)
∧-reflexivity′ {a} {b} a≡b rewrite cong (_∧ a) a≡b
                                 | cong (b ∧_) a≡b
                                 = refl



--compositional stability: substitution
∧-substitution : ∀ {a b c} → a ≡ b → (c ∧ a) ≡ (c ∧ b)
∧-substitution refl = refl

∧-substitution′ : ∀ {a b c} → a ≡ b → (c ∧ a) ≡ (c ∧ b)
∧-substitution′ {a} {b} {c} a≡b rewrite cong (c ∧_) a≡b = refl



--soundness
--I output of an and gate implies that both of its inputs must also be I
--O output of an and gate implies that one of its inputs must be O
∧-soundnessˡ : ∀ a → a ∧ I ≡ I → a ≡ I
∧-soundnessˡ I out-I = refl

∧-soundnessʳ : ∀ b → I ∧ b ≡ I → b ≡ I
∧-soundnessʳ I out-I = refl

∧-soundness-I : ∀ a b → a ∧ b ≡ I → a ≡ I × b ≡ I
∧-soundness-I I I out-I = ⟨ refl , refl ⟩

∧-soundness-O : ∀ a b → a ∧ b ≡ O → a ≡ O ⊎ b ≡ O
∧-soundness-O O b out-O = inj₁ refl
∧-soundness-O I O out-O = inj₂ refl



--absorption
a∧[¬a∧b]≡O : ∀ a b → a ∧ (¬ a ∧ b) ≡ O
a∧[¬a∧b]≡O a b rewrite ∧-assoc a (¬ a) b
                     | b∧¬b≡O a
                     = refl

a∧[b∧¬a]≡O : ∀ a b → a ∧ (b ∧ ¬ a) ≡ O
a∧[b∧¬a]≡O a b rewrite ∧-comm b (¬ a)
                     | a∧[¬a∧b]≡O a b
                     = refl
