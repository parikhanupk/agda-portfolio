module HardwareVerification.NotGate where



open import HardwareVerification.Bit using (Bit; low; high)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)



¬ : Bit → Bit
¬ low  = high
¬ high = low



--truth table conformance
not-low : ¬ low ≡ high
not-low = refl

not-high : ¬ high ≡ low
not-high = refl



--part of verification would be to prove involution (the double-not law), or two not gates cancel out
not-involution : ∀ (b : Bit) → ¬ (¬ b) ≡ b
not-involution low  = refl
not-involution high = refl



--proof that input and output are never same
not-distinction : ∀ (b : Bit) → ¬ b ≢ b
not-distinction low ()
not-distinction high ()



--if outputs of two not-gates are same it implies that inputs must have been the same
not-injective : ∀ (a b : Bit) → ¬ a ≡ ¬ b → a ≡ b
not-injective low low high≡high = refl
not-injective high high low≡low = refl



--surjectivity (existence) proof that every possible state can be reached by the gate
not-surjective : ∀ (b : Bit) → ∃[ c ] (¬ c ≡ b)
not-surjective low = ⟨ high , refl ⟩
not-surjective high = ⟨ low , refl ⟩



--absence of fixed point, proof that there is no stable bit that stays the same when inverted
not-distinction‵ : ∀ (b : Bit) → (¬ b ≡ b) → ⊥
not-distinction‵ low ()
not-distinction‵ high ()

not-distinction‵‵ : ∃[ b ] (¬ b ≡ b) → ⊥
not-distinction‵‵ ⟨ low , () ⟩
not-distinction‵‵ ⟨ high , () ⟩
