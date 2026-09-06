module Series.Naturals where



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)



naturalsᵣ : ℕ → List ℕ
naturalsᵣ zero = 0 ∷ []
naturalsᵣ (suc n) = (suc n) ∷ (naturalsᵣ n)

_ : naturalsᵣ 0 ≡ 0 ∷ []
_ = refl

_ : naturalsᵣ 3 ≡ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
_ = refl

_ : sum (naturalsᵣ 3) ≡ 6
_ = refl



naturals-acc : (n : ℕ) → (acc : List ℕ) → List ℕ
naturals-acc zero acc = 0 ∷ acc
naturals-acc (suc n) acc = naturals-acc n ((suc n) ∷ acc)

naturalsₐ : (n : ℕ) → List ℕ
naturalsₐ n = naturals-acc n []

_ : naturalsₐ 0 ≡ 0 ∷ []
_ = refl

_ : naturalsₐ 3 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : sum (naturalsₐ 3) ≡ 6
_ = refl
