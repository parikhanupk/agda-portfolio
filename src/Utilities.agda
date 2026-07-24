module Utilities where



open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _<ᵇ_; _≤_; z≤n; s≤s; _∸_; _≥_)
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



s[a∸b]≡sa∸b : ∀ (a b : ℕ) → b ≤ a → suc (a ∸ b) ≡ suc a ∸ b
s[a∸b]≡sa∸b a zero _ = refl
s[a∸b]≡sa∸b (suc a) (suc b) (s≤s b≤a) = s[a∸b]≡sa∸b a b b≤a

a≤b→a≤sb : ∀ (a b : ℕ) → a ≤ b → a ≤ suc b
a≤b→a≤sb zero b _ = z≤n
a≤b→a≤sb (suc a) (suc b) (s≤s a≤b) = s≤s (a≤b→a≤sb a b a≤b)

a≤c≤b→c∸a≤b : ∀ (a b c : ℕ) → a ≤ c → c ≤ b → c ∸ a ≤ b
a≤c≤b→c∸a≤b zero b c _ c≤b = c≤b
a≤c≤b→c∸a≤b (suc a) (suc b) (suc c) (s≤s a≤c) (s≤s c≤b) = a≤b→a≤sb (suc c ∸ suc a) b (a≤c≤b→c∸a≤b a b c a≤c c≤b)

a+[b∸c]≡b∸[c∸a] : ∀ (a b c : ℕ) → a ≤ c → c ≤ b → a + (b ∸ c) ≡ b ∸ (c ∸ a)
a+[b∸c]≡b∸[c∸a] zero b c _ _ = refl
a+[b∸c]≡b∸[c∸a] (suc a) (suc b) (suc c) (s≤s a≤c) (s≤s c≤b) =
  begin
    suc a + (suc b ∸ suc c)
  ≡⟨ refl ⟩
    suc (a + (b ∸ c))
  ≡⟨ cong suc (a+[b∸c]≡b∸[c∸a] a b c a≤c c≤b) ⟩
    suc (b ∸ (c ∸ a))
  ≡⟨ s[a∸b]≡sa∸b b (c ∸ a) (a≤c≤b→c∸a≤b a b c a≤c c≤b) ⟩
    suc b ∸ (c ∸ a)
  ∎



a≤b→a≤b+c : ∀ (a b c : ℕ) → a ≤ b → a ≤ b + c
a≤b→a≤b+c zero b c z≤n = z≤n
a≤b→a≤b+c (suc a) (suc b) c (s≤s a≤b) = s≤s (a≤b→a≤b+c a b c a≤b)



c≥1→a≤b→a≤b*c : ∀ (a b c : ℕ) → c ≥ 1 → a ≤ b → a ≤ b * c
c≥1→a≤b→a≤b*c zero zero (suc c) (s≤s z≤n) z≤n = z≤n
c≥1→a≤b→a≤b*c zero (suc b) (suc c) (s≤s z≤n) z≤n = z≤n
c≥1→a≤b→a≤b*c (suc a) (suc b) (suc c) (s≤s z≤n) (s≤s a≤b)
              rewrite *-comm b (suc c)
                    | sym (+-assoc c b (c * b))
                    | +-comm c b
                    | +-assoc b c (c * b)
                    = s≤s (a≤b→a≤b+c a b (c + c * b) a≤b)

a≤a : ∀ (a : ℕ) → a ≤ a
a≤a zero = z≤n
a≤a (suc a) = s≤s (a≤a a)

a≤a*b : ∀ (a b : ℕ) → b ≥ 1 → a ≤ a * b
a≤a*b a b b≥1 = c≥1→a≤b→a≤b*c a a b b≥1 (a≤a a)

ab≥1 : ∀ (a b : ℕ) → a ≥ 1 → b ≥ 1 → a * b ≥ 1
ab≥1 _ _ (s≤s _) (s≤s _) = s≤s z≤n

saⁿ≥1 : ∀ (a n : ℕ) → suc a ^ n ≥ 1
saⁿ≥1 a zero = s≤s z≤n
saⁿ≥1 a (suc n) = ab≥1 (suc a) (suc a ^ n) (s≤s z≤n) (saⁿ≥1 a n)

a≤aˢⁿ : ∀ (a n : ℕ) → a ≤ a ^ (suc n)
a≤aˢⁿ zero n = z≤n
a≤aˢⁿ (suc a) n = a≤a*b (suc a) (suc a ^ n) (saⁿ≥1 a n)
