module Naturals.Properties.EvenOdd where



open import Data.Nat using (ℕ; zero; suc; _+_; _≥_; _≤_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Product using (∃-syntax; _×_; _,_)



data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  eo : Even zero
  es : ∀ {n : ℕ} → Odd n → Even (suc n)

data Odd where
  os : ∀ {n : ℕ} → Even n → Odd (suc n)



even+even≡even : ∀ {a b : ℕ} → Even a → Even b → Even (a + b)
even+even≡even {.(zero)} {b} eo even-b = even-b
even+even≡even {.(suc (suc n))} {b} (es (os {n} even-n)) even-b = es (os (even+even≡even even-n even-b))



even+odd≡odd : ∀ {a b : ℕ} → Even a → Odd b → Odd (a + b)
even+odd≡odd {.(zero)} {b} eo odd-b = odd-b
even+odd≡odd {.(suc (suc n))} {b} (es (os {n} even-n)) odd-b = os (es (even+odd≡odd even-n odd-b))



odd+even≡odd : ∀ {a b : ℕ} → Odd a → Even b → Odd (a + b)
odd+even≡odd {a} {b} odd-a even-b = subst Odd (+-comm b a) (even+odd≡odd even-b odd-a)



odd+odd≡even : ∀ {a b : ℕ} → Odd a → Odd b → Even (a + b)
odd+odd≡even {.(suc a')} {.(suc b')} (os {a'} even-a') (os {b'} even-b')
             rewrite +-comm a' (suc b') = es (os (even+even≡even even-b' even-a'))



*-evenˡ : ∀ {a b : ℕ} → Even a → Even (a * b)
*-evenˡ {a} {zero} even-a rewrite *-comm a zero = eo
*-evenˡ {a} {suc b} even-a rewrite *-comm a (suc b) = even+even≡even even-a (subst Even (*-comm a b) (*-evenˡ even-a))

*-evenʳ : ∀ {a b : ℕ} → Even a → Even (b * a)
*-evenʳ {a} {b} even-a = subst Even (*-comm a b) (*-evenˡ even-a)
