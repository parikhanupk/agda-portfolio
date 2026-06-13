module HardwareVerification.NandGate where



open import HardwareVerification.Bit using (Bit; O; I)
open import HardwareVerification.NotGate using (¬)
open import HardwareVerification.AndGate using (_∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import HardwareVerification.OrGate using (_∨_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)



_⊼_ : Bit → Bit → Bit
a ⊼ b = ¬ (a ∧ b)

infixr 6 _⊼_



--truth table conformance
_ : O ⊼ O ≡ I
_ = refl

_ : O ⊼ I ≡ I
_ = refl

_ : I ⊼ O ≡ I
_ = refl

_ : I ⊼ I ≡ O
_ = refl



⊼-comm : ∀ (a b : Bit) → a ⊼ b ≡ b ⊼ a
⊼-comm O O = refl
⊼-comm O I = refl
⊼-comm I O = refl
⊼-comm I I = refl



--non associativity
⊼-non-assoc : (∀ (a b c : Bit) → a ⊼ (b ⊼ c) ≡ (a ⊼ b) ⊼ c) → ⊥
⊼-non-assoc x with x O O I
...              | ()



--inverted identity
b⊼b≡¬b : ∀ b → b ⊼ b ≡ ¬ b
b⊼b≡¬b O = refl
b⊼b≡¬b I = refl



--one fixed input
b⊼O≡I : ∀ b → b ⊼ O ≡ I
b⊼O≡I O = refl
b⊼O≡I I = refl

b⊼I≡¬b : ∀ b → b ⊼ I ≡ ¬ b
b⊼I≡¬b O = refl
b⊼I≡¬b I = refl



--nand contradiction: nand of a signal with its complement
b⊼¬b≡I : ∀ b → b ⊼ ¬ b ≡ I
b⊼¬b≡I O = refl
b⊼¬b≡I I = refl



--nand is universal
⊼-uni-¬ : ∀ b → b ⊼ b ≡ ¬ b
⊼-uni-¬ O = refl
⊼-uni-¬ I = refl

⊼-uni-∧ : ∀ a b → (a ⊼ b) ⊼ (a ⊼ b) ≡ a ∧ b
⊼-uni-∧ O b = refl
⊼-uni-∧ I O = refl
⊼-uni-∧ I I = refl

⊼-uni-∨ : ∀ a b → (a ⊼ a) ⊼ (b ⊼ b) ≡ a ∨ b
⊼-uni-∨ O O = refl
⊼-uni-∨ O I = refl
⊼-uni-∨ I b = refl

--single input nand representating a single nand gate with both inputs tied to a single input signal
--that is - not gate, but not gate in this form is a single nand
⊼¹_ : Bit → Bit
⊼¹ b = b ⊼ b

⊼¹-uni-¬ : ∀ b → ⊼¹ b ≡ ¬ b
⊼¹-uni-¬ b = ⊼-uni-¬ b

⊼¹-uni-∧ : ∀ a b → ⊼¹ (a ⊼ b) ≡ a ∧ b
⊼¹-uni-∧ a b rewrite ⊼-uni-∧ a b = refl

⊼¹-uni-∨ : ∀ a b → (⊼¹ a) ⊼ (⊼¹ b) ≡ a ∨ b
⊼¹-uni-∨ a b rewrite ⊼-uni-∨ a b = refl



--not nand is and
¬[a⊼b]≡a∧b : ∀ a b → ¬ (a ⊼ b) ≡ a ∧ b
¬[a⊼b]≡a∧b O b = refl
¬[a⊼b]≡a∧b I O = refl
¬[a⊼b]≡a∧b I I = refl



--not and is nand
¬[a∧b]≡a⊼b : ∀ a b → ¬ (a ∧ b) ≡ a ⊼ b
¬[a∧b]≡a⊼b O b = refl
¬[a∧b]≡a⊼b I O = refl
¬[a∧b]≡a⊼b I I = refl



--double negation compatibility
¬[¬[a⊼b]]≡a⊼b : ∀ (a b : Bit) → ¬ (¬ (a ⊼ b)) ≡ a ⊼ b
¬[¬[a⊼b]]≡a⊼b O b = refl
¬[¬[a⊼b]]≡a⊼b I O = refl
¬[¬[a⊼b]]≡a⊼b I I = refl

¬[¬[a⊼b]]≡a⊼b′ : ∀ (a b : Bit) → ¬ (¬ (a ⊼ b)) ≡ a ⊼ b
¬[¬[a⊼b]]≡a⊼b′ a b rewrite cong ¬ (¬[a⊼b]≡a∧b a b)
                         | ¬[a∧b]≡a⊼b a b
                         = refl



--inversion symmetry (if two wires are opposites their ⊼ is always I)
a≢b→a⊼b≡I : ∀ a b → (a ≢ b) → (a ⊼ b ≡ I)
a≢b→a⊼b≡I O b a≢b = refl
a≢b→a⊼b≡I I O a≢b = refl
a≢b→a⊼b≡I I I a≢b = ⊥-elim (a≢b refl)



--compositional stability: congruence (if sub-circuits are equivalent, ⊼ preserves that equivalence)
⊼-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ⊼ c) ≡ (b ⊼ d)
⊼-congruence {a} {b} {c} {d} a≡b c≡d rewrite cong (_⊼ c) a≡b
                                           | cong (b ⊼_) c≡d
                                           = refl



--compositional stability: reflexivity of ⊼
⊼-reflexivity : ∀ {a b} → a ≡ b → (a ⊼ a) ≡ (b ⊼ b)
⊼-reflexivity {a} {b} a≡b rewrite cong (_⊼ a) a≡b
                                | cong (b ⊼_) a≡b
                                = refl



--compositional stability: substitution
⊼-substitution : ∀ {a b c} → a ≡ b → (c ⊼ a) ≡ (c ⊼ b)
⊼-substitution {a} {b} {c} a≡b rewrite cong (c ⊼_) a≡b = refl



--soundness
--I output of a nand gate implies that at least one of its inputs must be O
--O output of a nand gate implies that both of its inputs must be I
⊼-soundness-I : ∀ a b → a ⊼ b ≡ I → a ≡ O ⊎ b ≡ O
⊼-soundness-I O b out-I = inj₁ refl
⊼-soundness-I I O out-I = inj₂ refl

⊼-soundness-O : ∀ a b → a ⊼ b ≡ O → a ≡ I × b ≡ I
⊼-soundness-O I I out-O = ⟨ refl , refl ⟩



--absorption
a⊼[¬a⊼b]≡¬a : ∀ a b → a ⊼ (¬ a ⊼ b) ≡ ¬ a
a⊼[¬a⊼b]≡¬a O b rewrite cong (O ⊼_) (⊼-comm I b) = refl
a⊼[¬a⊼b]≡¬a I b = refl

a⊼[b⊼¬a]≡¬a : ∀ a b → a ⊼ (b ⊼ ¬ a) ≡ ¬ a
a⊼[b⊼¬a]≡¬a a b rewrite cong (a ⊼_) (⊼-comm b (¬ a))
                      | a⊼[¬a⊼b]≡¬a a b
                      = refl
