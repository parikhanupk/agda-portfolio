module HardwareVerification.AndGate where



open import HardwareVerification.Bit using (Bit; low; high)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open import HardwareVerification.NotGate using (¬; not-involution)
open import Data.Empty using (⊥-elim)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)



_∧_ : Bit → Bit → Bit
low ∧ b = low
high ∧ b = b

infixr 6 _∧_



--truth table conformance
_ : low ∧ low ≡ low
_ = refl

_ : low ∧ high ≡ low
_ = refl

_ : high ∧ low ≡ low
_ = refl

_ : high ∧ high ≡ high
_ = refl



and-comm : ∀ (a b : Bit) → a ∧ b ≡ b ∧ a
and-comm low low = refl
and-comm low high = refl
and-comm high low = refl
and-comm high high = refl



and-assoc : ∀ (a b c : Bit) → a ∧ (b ∧ c) ≡ (a ∧ b) ∧ c
and-assoc low b c = refl
and-assoc high b c = refl



and-idempotent : ∀ (b : Bit) → b ∧ b ≡ b
and-idempotent low = refl
and-idempotent high = refl



--high ∧ b ≡ b is definitional
and-identityˡ : ∀ (b : Bit) → high ∧ b ≡ b
and-identityˡ b = refl

and-identityʳ : ∀ (b : Bit) → b ∧ high ≡ b
and-identityʳ b rewrite and-comm b high = refl



--low ∧ b ≡ low is definitional
and-annihilationˡ : ∀ (b : Bit) → low ∧ b ≡ low
and-annihilationˡ b = refl

and-annihilationʳ : ∀ (b : Bit) → b ∧ low ≡ low
and-annihilationʳ b rewrite and-comm b low = refl



and-contradiction : ∀ (b : Bit) → b ∧ ¬ b ≡ low
and-contradiction low = refl
and-contradiction high = refl



and-inverted-identity : ∀ (b : Bit) → ¬ (b ∧ high) ≡ ¬ b
and-inverted-identity low = refl
and-inverted-identity high = refl



and-inverted-annihilation : ∀ (b : Bit) → ¬ (b ∧ low) ≡ high
and-inverted-annihilation low = refl
and-inverted-annihilation high = refl



and-double-negation-compat : ∀ (a b : Bit) → ¬ (¬ (a ∧ b)) ≡ a ∧ b
and-double-negation-compat low b = refl
and-double-negation-compat high b rewrite not-involution b = refl



--inversion symmetry (if two wires are opposites their ∧ is always low)
and-inversion-symmetry : ∀ a b → (a ≢ b) → (a ∧ b ≡ low)
and-inversion-symmetry low b a≢b = refl
and-inversion-symmetry high low a≢b = refl
and-inversion-symmetry high high a≢b = ⊥-elim (a≢b refl)



--compositional stability: congruence (if sub-circuits are equivalent, ∧ preserves that equivalence)
and-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
and-congruence refl refl = refl

and-congruence′ : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
and-congruence′ {a} {b} {c} {d} a≡b c≡d =
  begin
    a ∧ c
  ≡⟨ cong (_∧ c) a≡b ⟩
    b ∧ c
  ≡⟨ cong (b ∧_) c≡d ⟩
    b ∧ d
  ∎



--compositional stability: reflexivity of ∧
and-reflexivity : ∀ {a b} → a ≡ b → (a ∧ a) ≡ (b ∧ b)
and-reflexivity refl = refl

and-reflexivity′ : ∀ {a b} → a ≡ b → (a ∧ a) ≡ (b ∧ b)
and-reflexivity′ {a} {b} a≡b rewrite cong (_∧ a) a≡b | cong (b ∧_) a≡b = refl



--compositional stability: substitution
and-substitution : ∀ {a b c} → a ≡ b → (c ∧ a) ≡ (c ∧ b)
and-substitution refl = refl

and-substitution′ : ∀ {a b c} → a ≡ b → (c ∧ a) ≡ (c ∧ b)
and-substitution′ {a} {b} {c} a≡b rewrite cong (c ∧_) a≡b = refl



--soundness
--high output of an and gate implies that both of its inputs must also be high
--low output of an and gate implies that one of its inputs must be low
and-soundnessˡ : ∀ a → a ∧ high ≡ high → a ≡ high
and-soundnessˡ high out-high = refl

and-soundnessʳ : ∀ b → high ∧ b ≡ high → b ≡ high
and-soundnessʳ high out-high = refl

and-soundness-high : ∀ a b → a ∧ b ≡ high → a ≡ high × b ≡ high
and-soundness-high high high out-high = ⟨ refl , refl ⟩

and-soundness-low : ∀ a b → a ∧ b ≡ low → a ≡ low ⊎ b ≡ low
and-soundness-low low b out-low = inj₁ refl
and-soundness-low high low out-low = inj₂ refl



--absorption
and-absorption₁ : ∀ a b → a ∧ (¬ a ∧ b) ≡ low
and-absorption₁ a b rewrite and-assoc a (¬ a) b
                          | and-contradiction a = refl

and-absorption₂ : ∀ a b → a ∧ (b ∧ ¬ a) ≡ low
and-absorption₂ a b rewrite and-comm b (¬ a)
                          | and-absorption₁ a b = refl
