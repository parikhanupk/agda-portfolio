module Naturals.Properties.EvenOdd where



open import Data.Nat using (ℕ; zero; suc; _+_; _≥_; _≤_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-identityʳ; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Naturals.Fibonacci using (fib)



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



even-a+a : ∀ (a : ℕ) → Even (a + a)
even-a+a zero = eo
even-a+a (suc a) rewrite +-comm a (suc a) = es (os (even-a+a a))



n+n+n≡3*n : ∀ (n : ℕ) → n + n + n ≡ 3 * n
n+n+n≡3*n zero = refl
n+n+n≡3*n (suc n) rewrite +-identityʳ n
                        | +-assoc n (suc n) (suc n)
                        = refl



fib-3n-is-even : ∀ (n : ℕ) → Even (fib (3 * n))
fib-3n-is-even zero = eo
fib-3n-is-even (suc n) rewrite +-identityʳ n
                             | +-comm n (suc n)
                             | +-comm n (suc (suc (n + n)))
                             | +-comm (fib (suc (n + n + n))) (fib (n + n + n))
                             | +-assoc (fib (n + n + n)) (fib (suc (n + n + n))) (fib (suc (n + n + n)))
                             = even+even≡even (subst Even (cong fib (sym (n+n+n≡3*n n))) (fib-3n-is-even n))
                                              (even-a+a (fib (suc (n + n + n))))
