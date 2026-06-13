module HardwareVerification.OrGate where



open import HardwareVerification.Bit using (Bit; O; I)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.NotGate using (¬; ¬¬b≡b)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import HardwareVerification.AndGate using (_∧_)



_∨_ : Bit → Bit → Bit
O ∨ b = b
I ∨ b = I

infixr 5 _∨_



--truth table conformance
_ : O ∨ O ≡ O
_ = refl

_ : O ∨ I ≡ I
_ = refl

_ : I ∨ O ≡ I
_ = refl

_ : I ∨ I ≡ I
_ = refl



∨-comm : ∀ (a b : Bit) → a ∨ b ≡ b ∨ a
∨-comm O O = refl
∨-comm O I = refl
∨-comm I O = refl
∨-comm I I = refl



∨-assoc : ∀ (a b c : Bit) → a ∨ (b ∨ c) ≡ (a ∨ b) ∨ c
∨-assoc O b c = refl
∨-assoc I b c = refl



--idempotence: redundant inputs can be treated as a single wire
b∨b≡b : ∀ (b : Bit) → b ∨ b ≡ b
b∨b≡b O = refl
b∨b≡b I = refl



--a pin tied to ground doesn't change the signal
∨-identityˡ : ∀ (b : Bit) → O ∨ b ≡ b
∨-identityˡ b = refl

∨-identityʳ : ∀ (b : Bit) → b ∨ O ≡ b
∨-identityʳ b rewrite ∨-comm b O = refl



--annihilation: a pin tied to Vcc forces the output to I
b∨I≡I : ∀ (b : Bit) → b ∨ I ≡ I
b∨I≡I b rewrite ∨-comm b I = refl



--contradiction, also known as the law of excluded middle in the context of classical logic
b∨¬b≡I : ∀ (b : Bit) → b ∨ ¬ b ≡ I
b∨¬b≡I O = refl
b∨¬b≡I I = refl



--inverted identity
¬[b∨O]≡¬b : ∀ (b : Bit) → ¬ (b ∨ O) ≡ ¬ b
¬[b∨O]≡¬b O = refl
¬[b∨O]≡¬b I = refl



--inverted annihilation
¬[b∨I]≡O : ∀ (b : Bit) → ¬ (b ∨ I) ≡ O
¬[b∨I]≡O O = refl
¬[b∨I]≡O I = refl



--double negation compatibility
¬[¬[a∨b]]≡a∨b : ∀ (a b : Bit) → ¬ (¬ (a ∨ b)) ≡ a ∨ b
¬[¬[a∨b]]≡a∨b O b rewrite ¬¬b≡b b = refl
¬[¬[a∨b]]≡a∨b I b = refl



--inversion symmetry (if two wires are opposites their ∨ is always I)
a≢b→a∨b≡I : ∀ a b → (a ≢ b) → (a ∨ b ≡ I)
a≢b→a∨b≡I O O a≢b = ⊥-elim (a≢b refl)
a≢b→a∨b≡I O I a≢b = refl
a≢b→a∨b≡I I b a≢b = refl



--compositional stability: congruence (if sub-circuits are equivalent, ∨ preserves that equivalence)
∨-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∨ c) ≡ (b ∨ d)
∨-congruence refl refl = refl

∨-congruence′ : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∨ c) ≡ (b ∨ d)
∨-congruence′ {a} {b} {c} {d} a≡b c≡d =
  begin
    a ∨ c
  ≡⟨ cong (_∨ c) a≡b ⟩
    b ∨ c
  ≡⟨ cong (b ∨_) c≡d ⟩
    b ∨ d
  ∎



--compositional stability: reflexivity of ∨
∨-reflexivity : ∀ {a b} → a ≡ b → (a ∨ a) ≡ (b ∨ b)
∨-reflexivity refl = refl

∨-reflexivity′ : ∀ {a b} → a ≡ b → (a ∨ a) ≡ (b ∨ b)
∨-reflexivity′ {a} {b} a≡b rewrite cong (_∨ a) a≡b
                                 | cong (b ∨_) a≡b
                                 = refl



--compositional stability: substitution
∨-substitution : ∀ {a b c} → a ≡ b → (c ∨ a) ≡ (c ∨ b)
∨-substitution refl = refl

∨-substitution′ : ∀ {a b c} → a ≡ b → (c ∨ a) ≡ (c ∨ b)
∨-substitution′ {a} {b} {c} a≡b rewrite cong (c ∨_) a≡b = refl



--soundness
--O output of an or gate implies that both of its inputs must also be O
--I output of an or gate implies that one of its inputs must be I
∨-soundnessˡ : ∀ a → a ∨ O ≡ O → a ≡ O
∨-soundnessˡ O out-O = refl

∨-soundnessʳ : ∀ b → O ∨ b ≡ O → b ≡ O
∨-soundnessʳ O out-O = refl

∨-soundness-I : ∀ a b → a ∨ b ≡ I → a ≡ I ⊎ b ≡ I
∨-soundness-I O I out-I = inj₂ refl
∨-soundness-I I b out-I = inj₁ refl

∨-soundness-O : ∀ a b → a ∨ b ≡ O → a ≡ O × b ≡ O
∨-soundness-O O O out-O = ⟨ refl , refl ⟩



--absorption
a∨[¬a∨b]≡I : ∀ a b → a ∨ (¬ a ∨ b) ≡ I
a∨[¬a∨b]≡I a b rewrite ∨-assoc a (¬ a) b
                     | b∨¬b≡I a
                     = refl

a∨[b∨¬a]≡I : ∀ a b → a ∨ (b ∨ ¬ a) ≡ I
a∨[b∨¬a]≡I a b rewrite ∨-comm b (¬ a)
                     | a∨[¬a∨b]≡I a b
                     = refl



--De Morgan's laws
¬[a∨b]≡¬a∧¬b : ∀ a b → ¬ (a ∨ b) ≡ (¬ a ∧ ¬ b)
¬[a∨b]≡¬a∧¬b O b = refl
¬[a∨b]≡¬a∧¬b I b = refl

¬[a∧b]≡¬a∨¬b : ∀ a b → ¬ (a ∧ b) ≡ (¬ a ∨ ¬ b)
¬[a∧b]≡¬a∨¬b O b = refl
¬[a∧b]≡¬a∨¬b I b = refl



--distributivity: ∨ over ∧
distrib-∨∧ : ∀ a b c → a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
distrib-∨∧ O b c = refl
distrib-∨∧ I b c = refl

--distributivity: ∧ over ∨
distrib-∧∨ : ∀ a b c → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
distrib-∧∨ O b c = refl
distrib-∧∨ I b c = refl



--absorption ∨ and ∧
a∨[a∧b]≡a : ∀ a b → a ∨ (a ∧ b) ≡ a
a∨[a∧b]≡a O b = refl
a∨[a∧b]≡a I b = refl

--absorption ∧ and ∨
a∧[a∨b]≡a : ∀ a b → a ∧ (a ∨ b) ≡ a
a∧[a∨b]≡a O b = refl
a∧[a∨b]≡a I b = refl



--redundancy
a∨[¬a∧b]≡a∨b : ∀ a b → a ∨ (¬ a ∧ b) ≡ a ∨ b
a∨[¬a∧b]≡a∨b O b = refl
a∨[¬a∧b]≡a∨b I b = refl



--consensus theorem, useful to drop (∨ (b ∧ c)) to simplify circuits
consensus : ∀ a b c → (a ∧ b) ∨ (¬ a ∧ c) ∨ (b ∧ c) ≡ (a ∧ b) ∨ (¬ a ∧ c)
consensus O O c rewrite ∨-identityʳ c = refl
consensus O I c rewrite b∨b≡b c = refl
consensus I O c = refl
consensus I I c = refl
