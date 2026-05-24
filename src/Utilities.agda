module Utilities where



open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)



∧-left : ∀ {a b : Bool} → a ∧ b ≡ true → a ≡ true
∧-left {true} {b} refl = refl

∧-right : ∀ {a b : Bool} → a ∧ b ≡ true → b ≡ true
∧-right {true} {true} refl = refl



all→rest : ∀ {A : Set} → (P : A → Bool) → (a : A) → (as : List A) → all P (a ∷ as) ≡ true → all P as ≡ true
all→rest P a as all-P-a∷as = ∧-right all-P-a∷as

all→head : ∀ {A : Set} → (P : A → Bool) → (a : A) → (as : List A) → all P (a ∷ as) ≡ true → P a ≡ true
all→head P a as all-P-a∷as = ∧-left all-P-a∷as

rest→all : ∀ {A : Set} → (P : A → Bool) → (a : A) → (as : List A) → P a ≡ true → all P as ≡ true → all P (a ∷ as) ≡ true
rest→all P a as Pa all-P-as = cong₂ _∧_ Pa all-P-as
{-
  begin
    all P (a ∷ as)
  ≡⟨⟩
    (P a) ∧ (all P as)
  ≡⟨ cong (_∧ (all P as)) Pa ⟩
    all P as
  ≡⟨ all-P-as ⟩
    true
  ∎
-}
