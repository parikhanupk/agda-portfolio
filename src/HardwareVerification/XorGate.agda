module HardwareVerification.XorGate where



open import HardwareVerification.Bit using (Bit; low; high)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; _≢_)
open import HardwareVerification.NotGate using (¬; not-involution)
open import Data.Empty using (⊥; ⊥-elim)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import HardwareVerification.AndGate using (_∧_; and-comm; and-contradiction; and-assoc; and-idempotent)
open import HardwareVerification.OrGate using (_∨_; or-comm; distrib-∨∧; or-contradiction; de-morgan-∧; de-morgan-∨; distrib-∧∨; or-identityʳ)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; _+_; _%_)
open import Data.Bool using (Bool; false; true)



_⊕_ : Bit → Bit → Bit
a ⊕ b = (a ∧ ¬ b) ∨ (¬ a ∧ b)

infixr 6 _⊕_



--truth table conformance
_ : low ⊕ low ≡ low
_ = refl

_ : low ⊕ high ≡ high
_ = refl

_ : high ⊕ low ≡ high
_ = refl

_ : high ⊕ high ≡ low
_ = refl



xor-comm : ∀ (a b : Bit) → a ⊕ b ≡ b ⊕ a
xor-comm low low = refl
xor-comm low high = refl
xor-comm high low = refl
xor-comm high high = refl



xor-identityˡ : ∀ b → low ⊕ b ≡ b
xor-identityˡ b =
  begin
    low ⊕ b
  ≡⟨⟩
    (low ∧ ¬ b) ∨ (¬ low ∧ b)
  ≡⟨⟩
    low ∨ (high ∧ b)
  ≡⟨⟩
    high ∧ b
  ≡⟨⟩
    b
  ∎

xor-identityʳ : ∀ b → b ⊕ low ≡ b
xor-identityʳ b rewrite xor-comm b low | xor-identityˡ b = refl



xor-assoc : ∀ a b c → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ c
xor-assoc low b c = refl
xor-assoc high low c = refl
xor-assoc high high low = refl
xor-assoc high high high = refl



--self-inverse (nilpotence)
xor-self-inverse : ∀ b → b ⊕ b ≡ low
xor-self-inverse low = refl
xor-self-inverse high = refl



--one fixed input
xor-fixed-high : ∀ b → b ⊕ high ≡ ¬ b
xor-fixed-high low = refl
xor-fixed-high high = refl

xor-fixed-low : ∀ b → b ⊕ low ≡ b
xor-fixed-low b rewrite xor-comm b low = refl



xor-double-inversion : ∀ a b → (¬ a ⊕ ¬ b) ≡ (a ⊕ b)
xor-double-inversion low low = refl
xor-double-inversion low high = refl
xor-double-inversion high low = refl
xor-double-inversion high high = refl

xor-double-inversion′ : ∀ a b → (¬ a ⊕ ¬ b) ≡ (a ⊕ b)
xor-double-inversion′ a b =
  begin
    ¬ a ⊕ ¬ b
  ≡⟨⟩
    (¬ a ∧ ¬ (¬ b)) ∨ (¬ (¬ a) ∧ ¬ b)
  ≡⟨ cong ((¬ a ∧ ¬ (¬ b)) ∨_) (cong (_∧ ¬ b) (not-involution a)) ⟩
    (¬ a ∧ ¬ (¬ b)) ∨ (a ∧ ¬ b)
  ≡⟨ cong (_∨ (a ∧ ¬ b)) (cong (¬ a ∧_) (not-involution b)) ⟩
    (¬ a ∧ b) ∨ (a ∧ ¬ b)
  ≡⟨ or-comm (¬ a ∧ b) (a ∧ ¬ b) ⟩
    (a ∧ ¬ b) ∨ (¬ a ∧ b)
  ≡⟨⟩
    a ⊕ b
  ∎



--argument negation
xor-arg-negationˡ : ∀ a b → ¬ (a ⊕ b) ≡ (¬ a ⊕ b)
xor-arg-negationˡ a b =
  begin
    ¬ (a ⊕ b)
  ≡⟨⟩
    ¬ ((a ∧ ¬ b) ∨ (¬ a ∧ b))
  ≡⟨ cong ¬ (distrib-∨∧ (a ∧ ¬ b) (¬ a) b) ⟩
    ¬ (((a ∧ ¬ b) ∨ ¬ a) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (or-comm (a ∧ ¬ b) (¬ a))) ⟩
    ¬ ((¬ a ∨ (a ∧ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (distrib-∨∧ (¬ a) a (¬ b))) ⟩
    ¬ (((¬ a ∨ a) ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (cong (_∧ (¬ a ∨ ¬ b)) (or-comm (¬ a) a))) ⟩
    ¬ (((a ∨ ¬ a) ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong (_∧ ((a ∧ ¬ b) ∨ b)) (cong (_∧ (¬ a ∨ ¬ b)) (or-contradiction a))) ⟩
    ¬ ((high ∧ (¬ a ∨ ¬ b)) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((a ∧ ¬ b) ∨ b))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (or-comm (a ∧ ¬ b) b)) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (b ∨ (a ∧ ¬ b)))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (distrib-∨∧ b a (¬ b))) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((b ∨ a) ∧ (b ∨ ¬ b)))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (cong ((b ∨ a) ∧_) (or-contradiction b))) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ ((b ∨ a) ∧ high))
  ≡⟨ cong ¬ (cong ((¬ a ∨ ¬ b) ∧_) (and-comm (b ∨ a) high)) ⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (high ∧ (b ∨ a)))
  ≡⟨⟩
    ¬ ((¬ a ∨ ¬ b) ∧ (b ∨ a))
  ≡⟨ cong ¬ (and-comm (¬ a ∨ ¬ b) (b ∨ a)) ⟩
    ¬ ((b ∨ a) ∧ (¬ a ∨ ¬ b))
  ≡⟨ cong ¬ (cong (_∧ (¬ a ∨ ¬ b)) (or-comm b a)) ⟩
    ¬ ((a ∨ b) ∧ (¬ a ∨ ¬ b))
  ≡⟨ de-morgan-∧ (a ∨ b) (¬ a ∨ ¬ b) ⟩
    ¬ (a ∨ b) ∨ ¬ (¬ a ∨ ¬ b)
  ≡⟨ cong (¬ (a ∨ b) ∨_) (de-morgan-∨ (¬ a) (¬ b)) ⟩
    ¬ (a ∨ b) ∨ (¬ (¬ a) ∧ ¬ (¬ b))
  ≡⟨ cong (¬ (a ∨ b) ∨_) (cong (_∧ ¬ (¬ b)) (not-involution a)) ⟩
    ¬ (a ∨ b) ∨ (a ∧ ¬ (¬ b))
  ≡⟨ cong (¬ (a ∨ b) ∨_) (cong (a ∧_) (not-involution b)) ⟩
    ¬ (a ∨ b) ∨ (a ∧ b)
  ≡⟨ cong (_∨ (a ∧ b)) (de-morgan-∨ a b) ⟩
    (¬ a ∧ ¬ b) ∨ (a ∧ b)
  ≡⟨ cong ((¬ a ∧ ¬ b) ∨_) (cong (_∧ b) (sym (not-involution a))) ⟩
    (¬ a ∧ ¬ b) ∨ (¬ (¬ a) ∧ b)
  ≡⟨⟩
    ¬ a ⊕ b
  ∎

xor-arg-negationʳ : ∀ a b → ¬ (a ⊕ b) ≡ (a ⊕ ¬ b)
xor-arg-negationʳ a b =
  begin
    ¬ (a ⊕ b)
  ≡⟨ cong ¬ (xor-comm a b) ⟩
    ¬ (b ⊕ a)
  ≡⟨ xor-arg-negationˡ b a ⟩
    ¬ b ⊕ a
  ≡⟨ xor-comm (¬ b) a ⟩
    a ⊕ ¬ b
  ∎



--xor of a signal with its complement
xor-contradiction : ∀ b → b ⊕ ¬ b ≡ high
xor-contradiction low = refl
xor-contradiction high = refl

--inversion symmetry (if two wires are opposites their ⊕ is always high)
xor-inversion-symmetry : ∀ a b → (a ≢ b) → (a ⊕ b ≡ high)
xor-inversion-symmetry low low a≢b = ⊥-elim (a≢b refl)
xor-inversion-symmetry low high a≢b = refl
xor-inversion-symmetry high low a≢b = refl
xor-inversion-symmetry high high a≢b = ⊥-elim (a≢b refl)



--double negation compatibility
xor-double-negation-compat : ∀ a b → ¬ (¬ (a ⊕ b)) ≡ a ⊕ b
xor-double-negation-compat a b =
  begin
    ¬ (¬ (a ⊕ b))
  ≡⟨⟩
    ¬ (¬ ((a ∧ ¬ b) ∨ (¬ a ∧ b)))
  ≡⟨ cong ¬ (de-morgan-∨ (a ∧ ¬ b) (¬ a ∧ b)) ⟩
    ¬ (¬ (a ∧ ¬ b) ∧ ¬ (¬ a ∧ b))
  ≡⟨ de-morgan-∧ (¬ (a ∧ ¬ b)) (¬ (¬ a ∧ b)) ⟩
    ¬ (¬ (a ∧ ¬ b)) ∨ ¬ (¬ (¬ a ∧ b))
  ≡⟨ cong (_∨ ¬ (¬ (¬ a ∧ b))) (not-involution (a ∧ ¬ b)) ⟩
    (a ∧ ¬ b) ∨ ¬ (¬ (¬ a ∧ b))
  ≡⟨ cong ((a ∧ ¬ b) ∨_) (not-involution (¬ a ∧ b)) ⟩
    (a ∧ ¬ b) ∨ (¬ a ∧ b)
  ≡⟨⟩
    a ⊕ b
  ∎



--compositional stability: congruence (if sub-circuits are equivalent, ⊕ preserves that equivalence)
xor-congruence : ∀ {a b c d} → a ≡ b → c ≡ d → (a ⊕ c) ≡ (b ⊕ d)
xor-congruence {a} {b} {c} {d} a≡b c≡d =
  begin
    a ⊕ c
  ≡⟨ cong (_⊕ c) a≡b ⟩
    b ⊕ c
  ≡⟨ cong (b ⊕_) c≡d ⟩
    b ⊕ d
  ∎



--compositional stability: reflexivity of ⊕
xor-reflexivity : ∀ {a b} → a ≡ b → (a ⊕ a) ≡ (b ⊕ b)
xor-reflexivity {a} {b} a≡b rewrite cong (_⊕ a) a≡b
                                  | cong (b ⊕_) a≡b = refl



--soundness
--high output of a xor gate implies that its inputs are complements of each other
--low output of a xor gate implies that its inputs are the same
xor-soundness-high : ∀ a b → a ⊕ b ≡ high → a ≢ b
xor-soundness-high low low ()
xor-soundness-high low high refl = λ ()
xor-soundness-high high low refl = λ ()
xor-soundness-high high high ()

xor-soundness-low : ∀ a b → a ⊕ b ≡ low → a ≡ b
xor-soundness-low low low refl = refl
xor-soundness-low low high ()
xor-soundness-low high low ()
xor-soundness-low high high refl = refl



--absorption
xor-absorption : ∀ a b → a ⊕ (a ⊕ b) ≡ b
xor-absorption a b =
  begin
    a ⊕ (a ⊕ b)
  ≡⟨ xor-assoc a a b ⟩
    (a ⊕ a) ⊕ b
  ≡⟨ cong (_⊕ b) (xor-self-inverse a) ⟩
    low ⊕ b
  ≡⟨⟩
    b
  ∎

xor-absorption-inv : ∀ a b → a ⊕ (¬ a ⊕ b) ≡ ¬ b
xor-absorption-inv a b =
  begin
    a ⊕ ¬ a ⊕ b
  ≡⟨ xor-assoc a (¬ a) b ⟩
    (a ⊕ ¬ a) ⊕ b
  ≡⟨ cong (_⊕ b) (xor-contradiction a) ⟩
    high ⊕ b
  ≡⟨ xor-comm high b ⟩
    b ⊕ high
  ≡⟨ xor-fixed-high b ⟩
    ¬ b
  ∎



xor-distrib-and : ∀ a b c → a ∧ (b ⊕ c) ≡ (a ∧ b) ⊕ (a ∧ c)
xor-distrib-and low b c = refl
xor-distrib-and high b c = refl



xor-neg-implies-x≡y : ∀ a b → ¬ (a ⊕ b) ≡ high → a ≡ b
xor-neg-implies-x≡y low low not-xor-high = refl
xor-neg-implies-x≡y high high not-xor-high = refl



xor-invertibility : ∀ a b c → (a ⊕ b ≡ c) → (c ⊕ b ≡ a) × (c ⊕ a ≡ b)
xor-invertibility low low low a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility low high high a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility high low high a⊕b≡c = ⟨ refl , refl ⟩
xor-invertibility high high low a⊕b≡c = ⟨ refl , refl ⟩



xor-as-programmable-inverter : ∀ b inv → (inv ≡ low × b ⊕ inv ≡ b) ⊎ (inv ≡ high × b ⊕ inv ≡ ¬ b)
xor-as-programmable-inverter b low = inj₁ ⟨ refl , xor-fixed-low b ⟩
xor-as-programmable-inverter b high = inj₂ ⟨ refl , xor-fixed-high b ⟩



xor-or-relation : ∀ a b → (a ⊕ b) ⊕ (a ∧ b) ≡ a ∨ b
xor-or-relation low low = refl
xor-or-relation low high = refl
xor-or-relation high low = refl
xor-or-relation high high = refl



xor-cancellationˡ : ∀ a b c → (a ⊕ b ≡ a ⊕ c) → b ≡ c
xor-cancellationˡ low low low x = refl
xor-cancellationˡ low high high x = refl
xor-cancellationˡ high low low x = refl
xor-cancellationˡ high high high x = refl

xor-cancellationʳ : ∀ a b c → (b ⊕ a ≡ c ⊕ a) → b ≡ c
xor-cancellationʳ a b c x rewrite xor-comm b a
                                | xor-comm c a
                                | xor-cancellationˡ a b c x = refl



--parity preservation where the high signal is treated as a one
odd-ones : (bs : List Bit) → (cur : Bool) → Bool
odd-ones [] cur = cur
odd-ones (low ∷ bs) cur = odd-ones bs cur
odd-ones (high ∷ bs) false = odd-ones bs true
odd-ones (high ∷ bs) true = odd-ones bs false

lemma₁ : ∀ b → low ⊕ b ≡ high → b ≡ high
lemma₁ high refl = refl

lemma₂ : ∀ b → high ⊕ b ≡ high → b ≡ low
lemma₂ low refl = refl

lemma₃ : ∀ b → low ⊕ b ≡ low → b ≡ low
lemma₃ low refl = refl

lemma₄ : ∀ b → high ⊕ b ≡ low → b ≡ high
lemma₄ high refl = refl

xor-parity : ∀ (bs : List Bit) → (foldr _⊕_ low bs) ≡ high → odd-ones bs false ≡ true
xor-parity (low ∷ bs) low-∷-out-high =
  begin
    odd-ones (low ∷ bs) false
  ≡⟨⟩
    odd-ones bs false
  ≡⟨ xor-parity bs (lemma₁ (foldr _⊕_ low bs) low-∷-out-high) ⟩
    true
  ∎
xor-parity (high ∷ bs) high-∷-out-high =
  begin
    odd-ones (high ∷ bs) false
  ≡⟨⟩
    odd-ones bs true
  ≡⟨ lemma₅ bs (lemma₂ (foldr _⊕_ low bs) high-∷-out-high) ⟩
    true
  ∎
  where
  lemma₅ : ∀ (bs : List Bit) → (foldr _⊕_ low bs) ≡ low → odd-ones bs true ≡ true
  lemma₅ [] refl = refl
  lemma₅ (low ∷ bs) p = lemma₅ bs (lemma₃ (foldr _⊕_ low bs) p)
  lemma₅ (high ∷ bs) p = xor-parity bs (lemma₄ (foldr _⊕_ low bs) p)
