module Naturals.Properties.Divisibility where



open import Data.Nat using (ℕ; zero; suc; _>_; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Divisibility.RuleB using (Div; dz; ds; ds-da→da; db→d[a*b]; da→db→d[a+b])
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



div-linear-combination : ∀ {d a b m n : ℕ} → (p : d > 0) → Div d p a → Div d p b → Div d p (m * a + n * b)
div-linear-combination {d} {a} {b} {m} {n} p da db = da→db→d[a+b] {d} {m * a} {n * b} p
                                                     (db→d[a*b] {d} {m} {a} p da)
                                                     (db→d[a*b] {d} {n} {b} p db)



a≤a+b : ∀ (a b : ℕ) → a ≤ a + b
a≤a+b zero b = z≤n
a≤a+b (suc a) b = s≤s (a≤a+b a b)



div-factor-bound : ∀ {d a : ℕ} → (p : d > 0) → (a>0 : a > 0) → Div d p a → d ≤ a
div-factor-bound {d} {.(d + n)} p a>0 (ds {n} da) = a≤a+b d n



--dec-div : ∀ {d a : ℕ} → (p : d > 0) → Div d p a ⊎ ¬ Div d p a
--dec-div {d} {a} p = {!!}

--d[a*b]→da-or-db : ∀ {d a b : ℕ} → (p : d > 0) → Div d p (a * b) → Div d p a ⊎ Div d p b
--d[a*b]→da-or-db {d} {a} {b} p d[a*b] = {!!}

--¬da→¬db→¬d[a*b] : ∀ {d a b : ℕ} → (p : d > 0) → ¬ Div d p a → ¬ Div d p b → ¬ Div d p (a * b)
--¬da→¬db→¬d[a*b] {d} {a} {b} p ¬da ¬db = {!!}
