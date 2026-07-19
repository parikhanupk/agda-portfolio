module Utilities where



open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _<ᵇ_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; *-identityʳ; *-assoc; *-comm; <⇒<ᵇ)



a≡b→Pb→Pa : ∀ {A : Set} → {a b : A} → (P : A → Set) → a ≡ b → P b → P a
a≡b→Pb→Pa P refl Pb = Pb



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



_² = _^ 2
_³ = _^ 3

a²≡a*a : ∀ (a : ℕ) → a ² ≡ a * a
a²≡a*a a rewrite *-identityʳ a = refl

a³≡a*a*a : ∀ (a : ℕ) → a ³ ≡ a * a * a
a³≡a*a*a a rewrite *-assoc a a a | a²≡a*a a = refl



+-swap : ∀ (a b c : ℕ) → a + b + c ≡ a + c + b
+-swap a b c rewrite +-assoc a b c
                   | +-comm b c
                   | sym (+-assoc a c b)
                   = refl



*-swap : ∀ (a b c : ℕ) → a * b * c ≡ a * c * b
*-swap a b c rewrite *-assoc a b c
                   | *-comm b c
                   | sym (*-assoc a c b)
                   = refl



a+[b+c]≡b+[a+c] : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
a+[b+c]≡b+[a+c] a b c rewrite sym (+-assoc a b c)
                            | +-comm a b
                            | +-assoc b a c
                            = refl




<→<ᵇ : ∀ {m n : ℕ} → m < n → (m <ᵇ n) ≡ true
<→<ᵇ (s≤s z≤n) = refl
<→<ᵇ (s≤s (s≤s m<n)) = <→<ᵇ (s≤s m<n)
