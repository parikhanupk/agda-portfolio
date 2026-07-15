module Naturals.Properties.Divisibility where



open import Data.Nat using (ℕ; zero; suc; _>_; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Divisibility.RuleB using (Div; dz; ds; ds-da→da)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Utilities using (a+[b+c]≡b+[a+c])
open import Data.Sum using (_⊎_; inj₁; inj₂)



da→¬db→¬d[a+b] : ∀ {d a b : ℕ} → (p : d > 0) → Div d p a → ¬ Div d p b → ¬ Div d p (a + b)
da→¬db→¬d[a+b] {d} {.(zero)} {b} p dz ¬db = ¬db
da→¬db→¬d[a+b] {d} {.(d + n)} {b} p (ds {n} dn) ¬db d[d+[n+b]] =
               da→¬db→¬d[a+b] p dn ¬db (ds-da→da p (subst (Div d p) (+-assoc d n b) d[d+[n+b]]))



¬da→db→¬d[a+b] : ∀ {d a b : ℕ} → (p : d > 0) → ¬ Div d p a → Div d p b → ¬ Div d p (a + b)
¬da→db→¬d[a+b] {d} {a} {.(zero)} p ¬da dz rewrite +-identityʳ a = ¬da
¬da→db→¬d[a+b] {d} {a} {.(d + n)} p ¬da (ds {n} db) d[a+[d+n]] =
               ¬da→db→¬d[a+b] p ¬da db (ds-da→da p (subst (Div d p) (a+[b+c]≡b+[a+c] a d n) d[a+[d+n]]))



¬da→¬ds-da : ∀ {d a : ℕ} → (p : d > 0) → ¬ Div d p a → ¬ Div d p (d + a)
¬da→¬ds-da {d} {a} p ¬da = λ ds-da → ¬da (ds-da→da p ds-da)



--dec-div : ∀ {d a : ℕ} → (p : d > 0) → Div d p a ⊎ ¬ Div d p a
--dec-div {d} {a} p = {!!}

--d[a*b]→da-or-db : ∀ {d a b : ℕ} → (p : d > 0) → Div d p (a * b) → Div d p a ⊎ Div d p b
--d[a*b]→da-or-db {d} {a} {b} p d[a*b] = {!!}

--¬da→¬db→¬d[a*b] : ∀ {d a b : ℕ} → (p : d > 0) → ¬ Div d p a → ¬ Div d p b → ¬ Div d p (a * b)
--¬da→¬db→¬d[a*b] {d} {a} {b} p ¬da ¬db = λ x → {!!}
