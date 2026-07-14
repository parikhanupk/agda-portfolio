module Divisibility.EuclideanRelation where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; z≤n; s≤s; _>_)
open import Data.Nat.Properties using (*-distribʳ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Utilities using (*-swap)



a<b→k+a<k+b : ∀ a b k → a < b → k + a < k + b
a<b→k+a<k+b a b zero p = p
a<b→k+a<k+b a b (suc k) p = s≤s (a<b→k+a<k+b a b k p)



a<b→ak<bk : ∀ a b k → k > 0 → a < b → a * k < b * k
a<b→ak<bk zero zero _ _ ()
a<b→ak<bk zero (suc b) (suc k) _ _ = s≤s z≤n
a<b→ak<bk (suc a) zero _ _ ()
a<b→ak<bk (suc a) (suc b) (suc k) sk>0 (s≤s a<b) = s≤s (a<b→k+a<k+b (a * suc k) (b * suc k) k (a<b→ak<bk a b (suc k) sk>0 a<b))



scaling : ∀ (a b q r k : ℕ)
          → k > 0
          → (a ≡ (b * q) + r) × (r < b)
          → (a * k ≡ ((b * k) * q) + (r * k)) × ((r * k) < (b * k))
scaling a b q r k k>0 a≡bq+r =
        helper a b q r k k>0 (proj₁ a≡bq+r) , a<b→ak<bk r b k k>0 (proj₂ a≡bq+r)
        where
        helper : ∀ a b q r k → k > 0 → a ≡ (b * q) + r → (a * k ≡ ((b * k) * q) + (r * k))
        helper a b q r k k>0 a≡bq+r =
          begin
            a * k
          ≡⟨ cong (_* k) a≡bq+r ⟩
            ((b * q) + r) * k
          ≡⟨ *-distribʳ-+ k (b * q) r ⟩
            ((b * q) * k) + (r * k)
          ≡⟨ cong (_+ (r * k)) (*-swap b q k) ⟩
            ((b * k) * q) + (r * k)
          ∎
