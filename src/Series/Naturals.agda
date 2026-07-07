module Series.Naturals where



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)



naturals-acc : (n : ℕ) → (acc : List ℕ) → List ℕ
naturals-acc zero acc = 0 ∷ acc
naturals-acc (suc n) acc = naturals-acc n ((suc n) ∷ acc)

naturals : (n : ℕ) → List ℕ
naturals n = naturals-acc n []

_ : naturals 0 ≡ 0 ∷ []
_ = refl

_ : naturals 3 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : sum (naturals 3) ≡ 6
_ = refl
