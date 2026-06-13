module HardwareVerification.XorGate where



open import HardwareVerification.Bit using (Bit; O; I)
open import HardwareVerification.NotGate using (¬; ¬¬b≡b)
open import HardwareVerification.AndGate using (_∧_; ∧-comm)
open import HardwareVerification.OrGate using (_∨_; ∨-comm; ¬[a∨b]≡¬a∧¬b; ¬[a∧b]≡¬a∨¬b; b∨¬b≡I; distrib-∨∧)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; _≢_)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Bool using (Bool; false; true)



_⊕_ : Bit → Bit → Bit
a ⊕ b = (a ∧ ¬ b) ∨ (¬ a ∧ b)

infixr 6 _⊕_



--truth table conformance
_ : O ⊕ O ≡ O
_ = refl

_ : O ⊕ I ≡ I
_ = refl

_ : I ⊕ O ≡ I
_ = refl

_ : I ⊕ I ≡ O
_ = refl



⊕-comm : ∀ (a b : Bit) → a ⊕ b ≡ b ⊕ a
⊕-comm O O = refl
⊕-comm O I = refl
⊕-comm I O = refl
⊕-comm I I = refl



⊕-identityˡ : ∀ b → O ⊕ b ≡ b
⊕-identityˡ b =
  begin O ⊕ b
  ≡⟨⟩ (O ∧ ¬ b) ∨ (¬ O ∧ b)
  ≡⟨⟩ O ∨ (I ∧ b)
  ≡⟨⟩ I ∧ b
  ≡⟨⟩ b
  ∎

⊕-identityʳ : ∀ b → b ⊕ O ≡ b
⊕-identityʳ b rewrite ⊕-comm b O
                    | ⊕-identityˡ b
                    = refl



⊕-assoc : ∀ a b c → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ c
⊕-assoc O b c = refl
⊕-assoc I O c = refl
⊕-assoc I I O = refl
⊕-assoc I I I = refl



--self-inverse (nilpotence)
b⊕b≡O : ∀ b → b ⊕ b ≡ O
b⊕b≡O O = refl
b⊕b≡O I = refl



--one fixed input
b⊕I≡¬b : ∀ b → b ⊕ I ≡ ¬ b
b⊕I≡¬b O = refl
b⊕I≡¬b I = refl

b⊕O≡b : ∀ b → b ⊕ O ≡ b
b⊕O≡b b rewrite ⊕-comm b O = refl



--inverted inputs
¬a⊕¬b≡a⊕b : ∀ a b → (¬ a ⊕ ¬ b) ≡ (a ⊕ b)
¬a⊕¬b≡a⊕b O O = refl
¬a⊕¬b≡a⊕b O I = refl
¬a⊕¬b≡a⊕b I O = refl
¬a⊕¬b≡a⊕b I I = refl

¬a⊕¬b≡a⊕b′ : ∀ a b → (¬ a ⊕ ¬ b) ≡ (a ⊕ b)
¬a⊕¬b≡a⊕b′ a b =
  begin
    ¬ a ⊕ ¬ b
  ≡⟨⟩
    (¬ a ∧ ¬ (¬ b)) ∨ (¬ (¬ a) ∧ ¬ b)
  ≡⟨ cong ((¬ a ∧ ¬ (¬ b)) ∨_) (cong (_∧ ¬ b) (¬¬b≡b a)) ⟩
    (¬ a ∧ ¬ (¬ b)) ∨ (a ∧ ¬ b)
  ≡⟨ cong (_∨ (a ∧ ¬ b)) (cong (¬ a ∧_) (¬¬b≡b b)) ⟩
    (¬ a ∧ b) ∨ (a ∧ ¬ b)
  ≡⟨ ∨-comm (¬ a ∧ b) (a ∧ ¬ b) ⟩
    (a ∧ ¬ b) ∨ (¬ a ∧ b)
  ≡⟨⟩
    a ⊕ b
  ∎



--argument negation
¬[a⊕b]≡¬a⊕b : ∀ a b → ¬ (a ⊕ b) ≡ (¬ a ⊕ b)
¬[a⊕b]≡¬a⊕b a b =
  begin
    ¬ (a ⊕ b)
  ≡⟨⟩
    ¬ ((a ∧ ¬ b) ∨ (¬ a ∧ b))
  ≡⟨ cong ¬ (distrib-∨∧ (a ∧ ¬ b) (¬ a) b) ⟩
    ¬ (((a ∧ ¬ b) ∨ ¬ a) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (∨-comm (a ∧ ¬ b) (¬ a))) ⟩
    ¬ ((¬ a ∨ (a ∧ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (distrib-∨∧ (¬ a) a (¬ b))) ⟩
    ¬ (((¬ a ∨ a) ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (cong (_∧ (¬ a ∨ ¬ b)) (∨-comm (¬ a) a))) ⟩
    ¬ (((a ∨ ¬ a) ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (cong (_∧ (¬ a ∨ ¬ b)) (b∨¬b≡I a))) ⟩
    ¬ ((I ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (∨-comm (a ∧ ¬ b) b)) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (b ∨ (a ∧ ¬ b)))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (distrib-∨∧ b a (¬ b))) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((b ∨ a) ∧ (b ∨ ¬ b)))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (cong ((b ∨ a) ∧_) (b∨¬b≡I b))) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((b ∨ a) ∧ I))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (∧-comm (b ∨ a) I)) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (I ∧ (b ∨ a)))
  ≡⟨⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (b ∨ a))
  ≡⟨ cong ¬ (∧-comm (¬ a ∨ ¬ b) (b ∨ a)) ⟩
    ¬ ((b ∨ a) ∧ (¬ a ∨ ¬ b))
  ≡⟨ cong ¬ (cong (_∧ (¬ a ∨ ¬ b)) (∨-comm b a)) ⟩
    ¬ ((a ∨ b) ∧ (¬ a ∨ ¬ b))
  ≡⟨ ¬[a∧b]≡¬a∨¬b (a ∨ b) (¬ a ∨ ¬ b) ⟩
    ¬ (a ∨ b) ∨ ¬ (¬ a ∨ ¬ b)
  ≡⟨ cong (¬ (a ∨ b) ∨_) (¬[a∨b]≡¬a∧¬b (¬ a) (¬ b)) ⟩
    ¬ (a ∨ b) ∨ (¬ (¬ a) ∧ ¬ (¬ b))
  ≡⟨ cong (¬ (a ∨ b) ∨_) (cong (_∧ ¬ (¬ b)) (¬¬b≡b a)) ⟩
    ¬ (a ∨ b) ∨ (a ∧ ¬ (¬ b))
  ≡⟨ cong (¬ (a ∨ b) ∨_) (cong (a ∧_) (¬¬b≡b b)) ⟩
    ¬ (a ∨ b) ∨ (a ∧ b)
  ≡⟨ cong (_∨ (a ∧ b)) (¬[a∨b]≡¬a∧¬b a b) ⟩
    (¬ a ∧ ¬ b) ∨ (a ∧ b)
  ≡⟨ cong ((¬ a ∧ ¬ b) ∨_) (cong (_∧ b) (sym (¬¬b≡b a))) ⟩
    (¬ a ∧ ¬ b) ∨ (¬ (¬ a) ∧ b)
  ≡⟨⟩
    ¬ a ⊕ b
  ∎

¬[a⊕b]≡a⊕¬b : ∀ a b → ¬ (a ⊕ b) ≡ (a ⊕ ¬ b)
¬[a⊕b]≡a⊕¬b a b =
  begin
    ¬ (a ⊕ b)
  ≡⟨ cong ¬ (⊕-comm a b) ⟩
    ¬ (b ⊕ a)
  ≡⟨ ¬[a⊕b]≡¬a⊕b b a ⟩
    ¬ b ⊕ a
  ≡⟨ ⊕-comm (¬ b) a ⟩
    a ⊕ ¬ b
  ∎



--⊕ of a signal with its complement
b⊕¬b≡I : ∀ b → b ⊕ ¬ b ≡ I
b⊕¬b≡I O = refl
b⊕¬b≡I I = refl

--inversion symmetry (if two wires are opposites their ⊕ is always I)
a≢b→a⊕b≡I : ∀ a b → (a ≢ b) → (a ⊕ b ≡ I)
a≢b→a⊕b≡I O O a≢b = ⊥-elim (a≢b refl)
a≢b→a⊕b≡I O I a≢b = refl
a≢b→a⊕b≡I I O a≢b = refl
a≢b→a⊕b≡I I I a≢b = ⊥-elim (a≢b refl)



--double negation compatibility
¬¬[a⊕b]≡a⊕b : ∀ a b → ¬ (¬ (a ⊕ b)) ≡ a ⊕ b
¬¬[a⊕b]≡a⊕b a b =
  begin
    ¬ (¬ (a ⊕ b))
  ≡⟨⟩
    ¬ (¬ ((a ∧ ¬ b) ∨ (¬ a ∧ b)))
  ≡⟨ cong ¬ (¬[a∨b]≡¬a∧¬b (a ∧ ¬ b) (¬ a ∧ b)) ⟩
    ¬ (¬ (a ∧ ¬ b) ∧ ¬ (¬ a ∧ b))
  ≡⟨ ¬[a∧b]≡¬a∨¬b (¬ (a ∧ ¬ b)) (¬ (¬ a ∧ b)) ⟩
    ¬ (¬ (a ∧ ¬ b)) ∨ ¬ (¬ (¬ a ∧ b))
  ≡⟨ cong (_∨ ¬ (¬ (¬ a ∧ b))) (¬¬b≡b (a ∧ ¬ b)) ⟩
    (a ∧ ¬ b) ∨ ¬ (¬ (¬ a ∧ b))
  ≡⟨ cong ((a ∧ ¬ b) ∨_) (¬¬b≡b (¬ a ∧ b)) ⟩
    (a ∧ ¬ b) ∨ (¬ a ∧ b)
  ≡⟨⟩
    a ⊕ b
  ∎



--compositional stability: congruence (if sub-circuits are equivalent, ⊕ preserves that equivalence)
⊕-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ⊕ c) ≡ (b ⊕ d)
⊕-congruence {a} {b} {c} {d} a≡b c≡d =
  begin
    a ⊕ c
  ≡⟨ cong (_⊕ c) a≡b ⟩
    b ⊕ c
  ≡⟨ cong (b ⊕_) c≡d ⟩
    b ⊕ d
  ∎



--compositional stability: reflexivity of ⊕
⊕-reflexivity : ∀ {a b} → a ≡ b → (a ⊕ a) ≡ (b ⊕ b)
⊕-reflexivity {a} {b} a≡b rewrite cong (_⊕ a) a≡b
                                | cong (b ⊕_) a≡b
                                = refl



--soundness
--I output of a xor gate implies that its inputs are complements of each other
--O output of a xor gate implies that its inputs are the same
⊕-soundness-I : ∀ a b → a ⊕ b ≡ I → a ≢ b
⊕-soundness-I O O ()
⊕-soundness-I O I refl = λ ()
⊕-soundness-I I O refl = λ ()
⊕-soundness-I I I ()

⊕-soundness-O : ∀ a b → a ⊕ b ≡ O → a ≡ b
⊕-soundness-O O O refl = refl
⊕-soundness-O O I ()
⊕-soundness-O I O ()
⊕-soundness-O I I refl = refl



--absorption
a⊕[a⊕b]≡b : ∀ a b → a ⊕ (a ⊕ b) ≡ b
a⊕[a⊕b]≡b a b =
  begin
    a ⊕ (a ⊕ b)
  ≡⟨ ⊕-assoc a a b ⟩
    (a ⊕ a) ⊕ b
  ≡⟨ cong (_⊕ b) (b⊕b≡O a) ⟩
    O ⊕ b
  ≡⟨⟩
    b
  ∎

a⊕[¬a⊕b]≡¬b : ∀ a b → a ⊕ (¬ a ⊕ b) ≡ ¬ b
a⊕[¬a⊕b]≡¬b a b =
  begin
    a ⊕ ¬ a ⊕ b
  ≡⟨ ⊕-assoc a (¬ a) b ⟩
    (a ⊕ ¬ a) ⊕ b
  ≡⟨ cong (_⊕ b) (b⊕¬b≡I a) ⟩
    I ⊕ b
  ≡⟨ ⊕-comm I b ⟩
    b ⊕ I
  ≡⟨ b⊕I≡¬b b ⟩
    ¬ b
  ∎



--distribution of ∧ over ⊕
distrib-∧⊕ : ∀ a b c → a ∧ (b ⊕ c) ≡ (a ∧ b) ⊕ (a ∧ c)
distrib-∧⊕ O b c = refl
distrib-∧⊕ I b c = refl



¬[a⊕b]≡I→a≡b : ∀ a b → ¬ (a ⊕ b) ≡ I → a ≡ b
¬[a⊕b]≡I→a≡b O O not-xor-I = refl
¬[a⊕b]≡I→a≡b I I not-xor-I = refl



xor-invertibility : ∀ a b c → (a ⊕ b ≡ c) → (c ⊕ b ≡ a) × (c ⊕ a ≡ b)
xor-invertibility O O O a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility O I I a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility I O I a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility I I O a⊕b≡c = ⟨ refl , refl ⟩



xor-as-programmable-inverter : ∀ b inv → (inv ≡ O × b ⊕ inv ≡ b) ⊎ (inv ≡ I × b ⊕ inv ≡ ¬ b)
xor-as-programmable-inverter b O = inj₁ ⟨ refl , b⊕O≡b b ⟩
xor-as-programmable-inverter b I = inj₂ ⟨ refl , b⊕I≡¬b b ⟩



xor-or-relation : ∀ a b → (a ⊕ b) ⊕ (a ∧ b) ≡ a ∨ b
xor-or-relation O O = refl
xor-or-relation O I = refl
xor-or-relation I O = refl
xor-or-relation I I = refl



xor-cancellationˡ : ∀ a b c → (a ⊕ b ≡ a ⊕ c) → b ≡ c
xor-cancellationˡ O O O x = refl
xor-cancellationˡ O I I x = refl
xor-cancellationˡ I O O x = refl
xor-cancellationˡ I I I x = refl

xor-cancellationʳ : ∀ a b c → (b ⊕ a ≡ c ⊕ a) → b ≡ c
xor-cancellationʳ a b c x rewrite ⊕-comm b a
                                | ⊕-comm c a
                                | xor-cancellationˡ a b c x
                                = refl



--parity preservation where the I signal is treated as a one
odd-ones : (bs : List Bit) → (cur : Bool) → Bool
odd-ones [] cur = cur
odd-ones (O ∷ bs) cur = odd-ones bs cur
odd-ones (I ∷ bs) false = odd-ones bs true
odd-ones (I ∷ bs) true = odd-ones bs false

O⊕b≡I→b≡I : ∀ b → O ⊕ b ≡ I → b ≡ I
O⊕b≡I→b≡I I refl = refl

I⊕b≡I→b≡O : ∀ b → I ⊕ b ≡ I → b ≡ O
I⊕b≡I→b≡O O refl = refl

O⊕b≡O→b≡O : ∀ b → O ⊕ b ≡ O → b ≡ O
O⊕b≡O→b≡O O refl = refl

I⊕b≡O→b≡I : ∀ b → I ⊕ b ≡ O → b ≡ I
I⊕b≡O→b≡I I refl = refl

xor-parity : ∀ (bs : List Bit) → (foldr _⊕_ O bs) ≡ I → odd-ones bs false ≡ true
xor-parity (O ∷ bs) O∷bs-outI =
  begin
    odd-ones (O ∷ bs) false
  ≡⟨⟩
    odd-ones bs false
  ≡⟨ xor-parity bs (O⊕b≡I→b≡I (foldr _⊕_ O bs) O∷bs-outI) ⟩
    true
  ∎
xor-parity (I ∷ bs) I∷bs-outI =
  begin
    odd-ones (I ∷ bs) false
  ≡⟨⟩
    odd-ones bs true
  ≡⟨ xor-parity⁰ bs (I⊕b≡I→b≡O (foldr _⊕_ O bs) I∷bs-outI) ⟩
    true
  ∎
  where
  xor-parity⁰ : ∀ (bs : List Bit) → (foldr _⊕_ O bs) ≡ O → odd-ones bs true ≡ true
  xor-parity⁰ [] refl = refl
  xor-parity⁰ (O ∷ bs) p = xor-parity⁰ bs (O⊕b≡O→b≡O (foldr _⊕_ O bs) p)
  xor-parity⁰ (I ∷ bs) p = xor-parity bs (I⊕b≡O→b≡I (foldr _⊕_ O bs) p)
