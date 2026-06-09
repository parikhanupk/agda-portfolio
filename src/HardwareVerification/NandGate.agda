module HardwareVerification.NandGate where



open import HardwareVerification.Bit using (Bit; low; high)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open import HardwareVerification.NotGate using (¬)
open import Data.Empty using (⊥; ⊥-elim)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.AndGate using (_∧_)
open import HardwareVerification.OrGate using (_∨_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)



_⊼_ : Bit → Bit → Bit
a ⊼ b = ¬ (a ∧ b)

infixr 6 _⊼_



--truth table conformance
_ : low ⊼ low ≡ high
_ = refl

_ : low ⊼ high ≡ high
_ = refl

_ : high ⊼ low ≡ high
_ = refl

_ : high ⊼ high ≡ low
_ = refl



nand-comm : ∀ (a b : Bit) → a ⊼ b ≡ b ⊼ a
nand-comm low low = refl
nand-comm low high = refl
nand-comm high low = refl
nand-comm high high = refl



--non associativity
nand-non-assoc : (∀ (a b c : Bit) → a ⊼ (b ⊼ c) ≡ (a ⊼ b) ⊼ c) → ⊥
nand-non-assoc x with x low low high
...                 | ()



--inverted identity
nand-inverted-identity : ∀ b → b ⊼ b ≡ ¬ b
nand-inverted-identity low = refl
nand-inverted-identity high = refl



--one fixed input
nand-fixed-low : ∀ b → b ⊼ low ≡ high
nand-fixed-low low = refl
nand-fixed-low high = refl

nand-fixed-high : ∀ b → b ⊼ high ≡ ¬ b
nand-fixed-high low = refl
nand-fixed-high high = refl



--nand of a signal with its complement
nand-contradiction : ∀ b → b ⊼ ¬ b ≡ high
nand-contradiction low = refl
nand-contradiction high = refl



--nand is universal
nand-uni-not : ∀ b → b ⊼ b ≡ ¬ b
nand-uni-not low = refl
nand-uni-not high = refl

nand-uni-and : ∀ a b → (a ⊼ b) ⊼ (a ⊼ b) ≡ a ∧ b
nand-uni-and low b = refl
nand-uni-and high low = refl
nand-uni-and high high = refl

--single input nand representating a single nand gate with both inputs tied to a single input signal
--that is - not gate, but not gate in this form is a single nand
_⊼¹ : Bit → Bit
_⊼¹ b = b ⊼ b

nand-uni-and₂ : ∀ a b → (a ⊼ b) ⊼¹ ≡ a ∧ b
nand-uni-and₂ a b rewrite nand-uni-and a b = refl

nand-uni-or : ∀ a b → a ∨ b ≡ (a ⊼¹) ⊼ (b ⊼¹)
nand-uni-or low low = refl
nand-uni-or low high = refl
nand-uni-or high b = refl



--not nand is and
not-nand-is-and : ∀ a b → ¬ (a ⊼ b) ≡ a ∧ b
not-nand-is-and low b = refl
not-nand-is-and high low = refl
not-nand-is-and high high = refl



--not and is nand
not-and-is-nand : ∀ a b → ¬ (a ∧ b) ≡ a ⊼ b
not-and-is-nand low b = refl
not-and-is-nand high low = refl
not-and-is-nand high high = refl



--double negation compatibility
nand-double-negation-compat : ∀ (a b : Bit) → ¬ (¬ (a ⊼ b)) ≡ a ⊼ b
nand-double-negation-compat low b = refl
nand-double-negation-compat high low = refl
nand-double-negation-compat high high = refl

nand-double-negation-compat′ : ∀ (a b : Bit) → ¬ (¬ (a ⊼ b)) ≡ a ⊼ b
nand-double-negation-compat′ a b rewrite cong ¬ (not-nand-is-and a b)
                                       | not-and-is-nand a b = refl



--inversion symmetry (if two wires are opposites their ⊼ is always high)
nand-inversion-symmetry : ∀ a b → (a ≢ b) → (a ⊼ b ≡ high)
nand-inversion-symmetry low b a≢b = refl
nand-inversion-symmetry high low a≢b = refl
nand-inversion-symmetry high high a≢b = ⊥-elim (a≢b refl)



--compositional stability: congruence (if sub-circuits are equivalent, ⊼ preserves that equivalence)
nand-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ⊼ c) ≡ (b ⊼ d)
nand-congruence {a} {b} {c} {d} a≡b c≡d rewrite cong (_⊼ c) a≡b | cong (b ⊼_) c≡d = refl



--compositional stability: reflexivity of ⊼
nand-reflexivity : ∀ {a b} → a ≡ b → (a ⊼ a) ≡ (b ⊼ b)
nand-reflexivity {a} {b} a≡b rewrite cong (_⊼ a) a≡b | cong (b ⊼_) a≡b = refl



--compositional stability: substitution
nand-substitution : ∀ {a b c} → a ≡ b → (c ⊼ a) ≡ (c ⊼ b)
nand-substitution {a} {b} {c} a≡b rewrite cong (c ⊼_) a≡b = refl



--soundness
--high output of a nand gate implies that at least one of its inputs must be low
--low output of a nand gate implies that both of its inputs must be high
nand-soundness-high : ∀ a b → a ⊼ b ≡ high → a ≡ low ⊎ b ≡ low
nand-soundness-high low b out-high = inj₁ refl
nand-soundness-high high low out-high = inj₂ refl

nand-soundness-low : ∀ a b → a ⊼ b ≡ low → a ≡ high × b ≡ high
nand-soundness-low high high out-low = ⟨ refl , refl ⟩



--absorption
nand-absorption₁ : ∀ a b → a ⊼ (¬ a ⊼ b) ≡ ¬ a
nand-absorption₁ low b rewrite cong (low ⊼_) (nand-comm high b) = refl
nand-absorption₁ high b = refl

nand-absorption₂ : ∀ a b → a ⊼ (b ⊼ ¬ a) ≡ ¬ a
nand-absorption₂ a b rewrite cong (a ⊼_) (nand-comm b (¬ a)) | nand-absorption₁ a b = refl
