module HardwareVerification.NotGate where



open import HardwareVerification.Bit using (Bit; O; I)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)



¬ : Bit → Bit
¬ O = I
¬ I = O



--truth table conformance
¬O : ¬ O ≡ I
¬O = refl

¬I : ¬ I ≡ O
¬I = refl



--part of verification would be to prove involution (the double-not law), or two not gates cancel out
¬¬b≡b : ∀ (b : Bit) → ¬ (¬ b) ≡ b
¬¬b≡b O = refl
¬¬b≡b I = refl



--proof that input and output are never same
¬b≢b : ∀ (b : Bit) → ¬ b ≢ b
¬b≢b O ()
¬b≢b I ()



--injectivity (if outputs of two not-gates are same it implies that inputs must have been the same)
¬a≡¬b→a≡b : ∀ (a b : Bit) → ¬ a ≡ ¬ b → a ≡ b
¬a≡¬b→a≡b O O refl = refl
¬a≡¬b→a≡b I I refl = refl



--surjectivity (existence) proof that every possible state can be reached by the gate
¬-surjective : ∀ (b : Bit) → ∃[ c ] (¬ c ≡ b)
¬-surjective O = ⟨ I , refl ⟩
¬-surjective I = ⟨ O , refl ⟩



--absence of fixed point, proof that there is no stable bit that stays the same when inverted
¬-distinction‵ : ∀ (b : Bit) → (¬ b ≡ b) → ⊥
¬-distinction‵ O ()
¬-distinction‵ I ()

¬-distinction‵‵ : ∃[ b ] (¬ b ≡ b) → ⊥
¬-distinction‵‵ ⟨ O , () ⟩
¬-distinction‵‵ ⟨ I , () ⟩
