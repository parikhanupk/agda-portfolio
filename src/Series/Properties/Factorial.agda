module Series.Properties.Factorial where



open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _>_)
open import Divisibility.RuleB using (Div; ds; dz; db→d[a*b]; da→d[a*b]; a→da)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Naturals.Factorial using (_!)



m≤n→m<n|m≡n : ∀ (m n : ℕ) → m ≤ n → (m < n) ⊎ (m ≡ n)
m≤n→m<n|m≡n zero zero _ = inj₂ refl
m≤n→m<n|m≡n zero (suc n) _ = inj₁ (s≤s z≤n)
m≤n→m<n|m≡n (suc m) (suc n) (s≤s m≤n)
  with m≤n→m<n|m≡n m n m≤n
...  | inj₁ wm<wn = inj₁ (s≤s wm<wn)
...  | inj₂ wm≡wn = inj₂ (cong suc wm≡wn)



m≤n→m|n! : ∀ (m n : ℕ) → (m>0 : m > 0) → m ≤ n → Div m m>0 (n !)
m≤n→m|n! (suc m) (suc n) (s≤s m≥0) (s≤s m≤n)
  with m≤n→m<n|m≡n m n m≤n
...  | inj₁ wm<wn = subst (Div (suc m) (s≤s m≥0)) refl
                          (db→d[a*b] {suc m} {suc n} {n !} (s≤s m≥0)
                                     (m≤n→m|n! (suc m) n (s≤s m≥0) wm<wn))
...  | inj₂ wm≡wn = subst (Div (suc m) (s≤s m≥0)) refl
                          (da→d[a*b] {suc m} {suc n} {n !} (s≤s m≥0)
                                     (subst (Div (suc m) (s≤s m≥0)) (cong suc wm≡wn) (a→da (s≤s m≥0))))
