module ComputationalTricks.Power2 where



open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)



data Bit : Set where
  O : Bit
  I : Bit

inc : List Bit → List Bit
inc [] = I ∷ []
inc (O ∷ bs) = I ∷ bs
inc (I ∷ bs) = O ∷ (inc bs)



_&_ : Bit → Bit → Bit
O & b = O
I & b = b

_&&_ : List Bit → List Bit → List Bit
[] && _ = []
(_ ∷ _) && [] = []
(a ∷ as) && (b ∷ bs) = (a & b) ∷ (as && bs)



b&b≡b : ∀ (b : Bit) → b & b ≡ b
b&b≡b O = refl
b&b≡b I = refl

bs&&bs≡bs : ∀ (bs : List Bit) → bs && bs ≡ bs
bs&&bs≡bs [] = refl
bs&&bs≡bs (b ∷ bs) rewrite b&b≡b b | bs&&bs≡bs bs = refl



data Zeros : List Bit → Set where
  zo : Zeros []
  zs : ∀ {bs} → Zeros bs → Zeros (O ∷ bs)



{-
data Pow2 : List Bit → Set where
  p2z : Pow2 (I ∷ [])
  p2s : ∀ {bs} → Pow2 bs → Pow2 (O ∷ bs)



lemma-zeros : ∀ (bs : List Bit) → Zeros bs → Pow2 (I ∷ bs)
lemma-zeros = {!!}



n&sn≡0→pow2-sn : ∀ (bs : List Bit)
               → Zeros (bs && inc bs)
               → Pow2 (inc bs)
n&sn≡0→pow2-sn [] _ = p2z
n&sn≡0→pow2-sn (O ∷ bs) (zs x) rewrite bs&&bs≡bs bs = lemma-zeros bs x
n&sn≡0→pow2-sn (I ∷ bs) (zs x) = p2s (n&sn≡0→pow2-sn bs x)
-}



data Pow2' : List Bit → Set where
  p2z : ∀ {bs} → Zeros bs → Pow2' (I ∷ bs) --a bit of a shortcut
  p2s : ∀ {bs} → Pow2' bs → Pow2' (O ∷ bs)



n&sn≡0→pow2-sn' : ∀ (bs : List Bit)
                → Zeros (bs && inc bs)
                → Pow2' (inc bs)
n&sn≡0→pow2-sn' [] _ = p2z zo
n&sn≡0→pow2-sn' (O ∷ bs) (zs x) rewrite bs&&bs≡bs bs = p2z x
n&sn≡0→pow2-sn' (I ∷ bs) (zs x) = p2s (n&sn≡0→pow2-sn' bs x)
