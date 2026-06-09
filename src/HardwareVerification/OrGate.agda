module HardwareVerification.OrGate where



open import HardwareVerification.Bit using (Bit; low; high)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open import HardwareVerification.NotGate using (¬; not-involution)
open import Data.Empty using (⊥-elim)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import HardwareVerification.AndGate using (_∧_)



_∨_ : Bit → Bit → Bit
low ∨ b = b
high ∨ b = high

infixr 5 _∨_



--truth table conformance
_ : low ∨ low ≡ low
_ = refl

_ : low ∨ high ≡ high
_ = refl

_ : high ∨ low ≡ high
_ = refl

_ : high ∨ high ≡ high
_ = refl



or-comm : ∀ (a b : Bit) → a ∨ b ≡ b ∨ a
or-comm low low = refl
or-comm low high = refl
or-comm high low = refl
or-comm high high = refl



or-assoc : ∀ (a b c : Bit) → a ∨ (b ∨ c) ≡ (a ∨ b) ∨ c
or-assoc low b c = refl
or-assoc high b c = refl



--redundant inputs can be treated as a single wire
or-idempotent : ∀ (b : Bit) → b ∨ b ≡ b
or-idempotent low = refl
or-idempotent high = refl



--a pin tied to ground doesn't change the signal
or-identityˡ : ∀ (b : Bit) → low ∨ b ≡ b
or-identityˡ b = refl

or-identityʳ : ∀ (b : Bit) → b ∨ low ≡ b
or-identityʳ b rewrite or-comm b low = refl



--a pin tied to Vcc forces the output to high
or-annihilation : ∀ (b : Bit) → b ∨ high ≡ high
or-annihilation b rewrite or-comm b high = refl



--contradiction, also known as the law of excluded middle in the context of classical logic
or-contradiction : ∀ (b : Bit) → b ∨ ¬ b ≡ high
or-contradiction low = refl
or-contradiction high = refl



or-inverted-identity : ∀ (b : Bit) → ¬ (b ∨ low) ≡ ¬ b
or-inverted-identity low = refl
or-inverted-identity high = refl



or-inverted-annihilation : ∀ (b : Bit) → ¬ (b ∨ high) ≡ low
or-inverted-annihilation low = refl
or-inverted-annihilation high = refl



--double negation compatibility
or-double-negation-compat : ∀ (a b : Bit) → ¬ (¬ (a ∨ b)) ≡ a ∨ b
or-double-negation-compat low b rewrite not-involution b = refl
or-double-negation-compat high b = refl



--inversion symmetry (if two wires are opposites their ∨ is always high)
or-inversion-symmetry : ∀ a b → (a ≢ b) → (a ∨ b ≡ high)
or-inversion-symmetry low low a≢b = ⊥-elim (a≢b refl)
or-inversion-symmetry low high a≢b = refl
or-inversion-symmetry high b a≢b = refl



--compositional stability: congruence (if sub-circuits are equivalent, ∨ preserves that equivalence)
or-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∨ c) ≡ (b ∨ d)
or-congruence refl refl = refl

or-congruence′ : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∨ c) ≡ (b ∨ d)
or-congruence′ {a} {b} {c} {d} a≡b c≡d =
  begin
    a ∨ c
  ≡⟨ cong (_∨ c) a≡b ⟩
    b ∨ c
  ≡⟨ cong (b ∨_) c≡d ⟩
    b ∨ d
  ∎



--compositional stability: reflexivity of ∨
or-reflexivity : ∀ {a b} → a ≡ b → (a ∨ a) ≡ (b ∨ b)
or-reflexivity refl = refl

or-reflexivity′ : ∀ {a b} → a ≡ b → (a ∨ a) ≡ (b ∨ b)
or-reflexivity′ {a} {b} a≡b rewrite cong (_∨ a) a≡b | cong (b ∨_) a≡b = refl



--compositional stability: substitution
or-substitution : ∀ {a b c} → a ≡ b → (c ∨ a) ≡ (c ∨ b)
or-substitution refl = refl

or-substitution′ : ∀ {a b c} → a ≡ b → (c ∨ a) ≡ (c ∨ b)
or-substitution′ {a} {b} {c} a≡b rewrite cong (c ∨_) a≡b = refl



--soundness
--low output of an or gate implies that both of its inputs must also be low
--high output of an or gate implies that one of its inputs must be high
or-soundnessˡ : ∀ a → a ∨ low ≡ low → a ≡ low
or-soundnessˡ low out-low = refl

or-soundnessʳ : ∀ b → low ∨ b ≡ low → b ≡ low
or-soundnessʳ low out-low = refl

or-soundness-high : ∀ a b → a ∨ b ≡ high → a ≡ high ⊎ b ≡ high
or-soundness-high low high out-high = inj₂ refl
or-soundness-high high b out-high = inj₁ refl

or-soundness-low : ∀ a b → a ∨ b ≡ low → a ≡ low × b ≡ low
or-soundness-low low low out-low = ⟨ refl , refl ⟩



--absorption
or-absorption₁ : ∀ a b → a ∨ (¬ a ∨ b) ≡ high
or-absorption₁ a b rewrite or-assoc a (¬ a) b
                         | or-contradiction a = refl

or-absorption₂ : ∀ a b → a ∨ (b ∨ ¬ a) ≡ high
or-absorption₂ a b rewrite or-comm b (¬ a)
                         | or-absorption₁ a b = refl



--De Morgan's laws
de-morgan-∨ : ∀ a b → ¬ (a ∨ b) ≡ (¬ a ∧ ¬ b)
de-morgan-∨ low b = refl
de-morgan-∨ high b = refl

de-morgan-∧ : ∀ a b → ¬ (a ∧ b) ≡ (¬ a ∨ ¬ b)
de-morgan-∧ low b = refl
de-morgan-∧ high b = refl



--distributivity: or over and
distrib-∨∧ : ∀ a b c → a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
distrib-∨∧ low b c = refl
distrib-∨∧ high b c = refl

--distributivity: and over or
distrib-∧∨ : ∀ a b c → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
distrib-∧∨ low b c = refl
distrib-∧∨ high b c = refl



--absorption ∨ and ∧
absorption-∨∧ : ∀ a b → a ∨ (a ∧ b) ≡ a
absorption-∨∧ low b = refl
absorption-∨∧ high b = refl

--absorption ∧ and ∨
absorption-∧∨ : ∀ a b → a ∧ (a ∨ b) ≡ a
absorption-∧∨ low b = refl
absorption-∧∨ high b = refl



--redundancy
redundancy : ∀ a b → a ∨ (¬ a ∧ b) ≡ a ∨ b
redundancy low b = refl
redundancy high b = refl



--consensus theorem, useful to drop (∨ (b ∧ c)) to simplify circuits
consensus : ∀ a b c → (a ∧ b) ∨ (¬ a ∧ c) ∨ (b ∧ c) ≡ (a ∧ b) ∨ (¬ a ∧ c)
consensus low low c rewrite or-identityʳ c = refl
consensus low high c rewrite or-idempotent c = refl
consensus high low c = refl
consensus high high c = refl
