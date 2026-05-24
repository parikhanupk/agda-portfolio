{-
Proofs around the Divisibility Rule of 2 on
1. base-10 list encoded naturals
   lines 134 and 207
2. algebraic "10a + b" encoded naturals
   lines 226 and 244
-}



module Divisibility.Rule2 where



open import Data.Nat using (ℕ; zero; suc; _+_; _^_; _*_; _<ᵇ_; _≥_; z≤n; s≤s; _>_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat.Properties using (+-identityʳ; *-comm)
open Relation.Binary.PropositionalEquality.≡-Reasoning



data Div2 : ℕ → Set where
  d2z : Div2 0
  d2s : ∀ {n : ℕ} → Div2 n → Div2 (suc (suc n))



d2a→d2b→d2[a+b] : ∀ (a b : ℕ) → Div2 a → Div2 b → Div2 (a + b)
d2a→d2b→d2[a+b] zero b d2z div2-b = div2-b
d2a→d2b→d2[a+b] (suc (suc a)) b (d2s div2-a) div2-b = d2s (d2a→d2b→d2[a+b] a b div2-a div2-b)



d2a→d2[a+b]→d2b : ∀ (a b : ℕ) → Div2 a → Div2 (a + b) → Div2 b
d2a→d2[a+b]→d2b zero _ _ div2-b = div2-b
d2a→d2[a+b]→d2b (suc (suc a)) b (d2s div2-a) (d2s div2-a+b) = d2a→d2[a+b]→d2b a b div2-a div2-a+b



d2a→d2[a*b] : ∀ (a b : ℕ) → Div2 a → Div2 (a * b)
d2a→d2[a*b] a zero div2-a rewrite *-comm a 0 = d2z
d2a→d2[a*b] a (suc b) div2-a rewrite *-comm a (suc b)
                                   | *-comm b a
                                   = d2a→d2b→d2[a+b] a (a * b) div2-a (d2a→d2[a*b] a b div2-a)



div2-10 : Div2 10
div2-10 = d2s (d2s (d2s (d2s (d2s d2z))))



a≥1→div2-10ᵃ : ∀ (a : ℕ) → a ≥ 1 → Div2 (10 ^ a)
a≥1→div2-10ᵃ (suc a) (s≤s a≥0) = d2a→d2[a*b] 10 (10 ^ a) div2-10



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



toℕ : (digits : List ℕ) → length digits > 0 → all (_<ᵇ 10) digits ≡ true → ℕ
toℕ (x ∷ []) _ _ = x
toℕ (x ∷ y ∷ digits) l>0 d<10 = ((10 ^ (length (y ∷ digits))) * x)
                              + toℕ (y ∷ digits) (s≤s z≤n) (all→rest (_<ᵇ 10) x (y ∷ digits) d<10)

_ : toℕ (0 ∷ []) (s≤s z≤n) refl ≡ 0
_ = refl

_ : toℕ (1 ∷ []) (s≤s z≤n) refl ≡ 1
_ = refl

_ : toℕ (1 ∷ 2 ∷ 3 ∷ []) (s≤s z≤n) refl ≡ 123
_ = refl



last : (digits : List ℕ) → length digits > 0 → all (_<ᵇ 10) digits ≡ true → ℕ
last (x ∷ []) _ _ = x
last (x ∷ y ∷ digits) _ d<10 = last (y ∷ digits) (s≤s z≤n) (all→rest (_<ᵇ 10) x (y ∷ digits) d<10)



lemma-div2-cons : ∀ (x : ℕ)
                  → (x<10 : (x <ᵇ 10) ≡ true)
                  → (digits : List ℕ)
                  → (l>0 : length digits > 0)
                  → (d<10 : all (_<ᵇ 10) digits ≡ true)
                  → Div2 (toℕ digits l>0 d<10)
                  → Div2 (toℕ (x ∷ digits) (s≤s z≤n) (rest→all (_<ᵇ 10) x digits x<10 d<10))
lemma-div2-cons x x<10 (y ∷ digits) (s≤s z≤n) d<10 div2-y∷digits =
                  d2a→d2b→d2[a+b] ((10 ^ length (y ∷ digits)) * x)
                                  (toℕ (y ∷ digits) (s≤s z≤n) d<10)
                                  (d2a→d2[a*b] (10 ^ length (y ∷ digits)) x (a≥1→div2-10ᵃ (length (y ∷ digits)) (s≤s z≤n)))
                                  div2-y∷digits



div-rule-2 : ∀ (decimal : List ℕ)
             → (l>0 : length decimal > 0)
             → (d<10 : all (_<ᵇ 10) decimal ≡ true)
             → Div2 (last decimal l>0 d<10)
             → Div2 (toℕ decimal l>0 d<10)
div-rule-2 (x ∷ []) _ _ div2-x = div2-x
div-rule-2 (x ∷ y ∷ decimal) l>0 d<10 div2-y∷decimal =
             lemma-div2-cons x
                             (all→head (_<ᵇ 10) x (y ∷ decimal) d<10)
                             (y ∷ decimal)
                             (s≤s z≤n)
                             (all→rest (_<ᵇ 10) x (y ∷ decimal) d<10)
                             (div-rule-2 (y ∷ decimal) (s≤s z≤n) (all→rest (_<ᵇ 10) x (y ∷ decimal) d<10) div2-y∷decimal)



digits18 : List ℕ
digits18 = 1 ∷ 8 ∷ []

--without div-rule-2
_ : Div2 (toℕ digits18 (s≤s z≤n) refl)
_ = d2s (d2s (d2s (d2s (d2s (d2s (d2s (d2s (d2s d2z))))))))

--with div-rule-2
_ : Div2 (toℕ digits18 (s≤s z≤n) refl)
_ = div-rule-2 digits18 (s≤s z≤n) refl (d2s (d2s (d2s (d2s d2z))))



digits20 : List ℕ
digits20 = 2 ∷ 0 ∷ []

--without div-rule-2
_ : Div2 (toℕ digits20 (s≤s z≤n) refl)
_ = d2s (d2s (d2s (d2s (d2s (d2s (d2s (d2s (d2s (d2s d2z)))))))))

--with div-rule-2
_ : Div2 (toℕ digits20 (s≤s z≤n) refl)
_ = div-rule-2 digits20 (s≤s z≤n) refl d2z



digits-big : List ℕ
digits-big = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

{-
--without div-rule-2
_ : Div2 (toℕ digits-big (s≤s z≤n) refl)
_ = {!!}
--as a demo, try doing the above using C-c C-a after putting "-t 60" or "-t 300" in the placeholder
-}

--with div-rule-2
_ : Div2 (toℕ digits-big (s≤s z≤n) refl)
_ = div-rule-2 digits-big (s≤s z≤n) refl (d2s (d2s (d2s d2z)))



lemma-div2-cons-inv : ∀ (x : ℕ)
                    → (x<10 : (x <ᵇ 10) ≡ true)
                    → (digits : List ℕ)
                    → (l>0 : length digits > 0)
                    → (d<10 : all (_<ᵇ 10) digits ≡ true)
                    → Div2 (toℕ (x ∷ digits) (s≤s z≤n) (rest→all (_<ᵇ 10) x digits x<10 d<10))
                    → Div2 (toℕ digits l>0 d<10)
lemma-div2-cons-inv x x<10 (y ∷ digits) (s≤s z≤n) d<10 div2-x∷y∷digits =
                    d2a→d2[a+b]→d2b ((10 ^ length (y ∷ digits)) * x)
                                    (toℕ (y ∷ digits) (s≤s z≤n) d<10)
                                    (d2a→d2[a*b] (10 ^ length (y ∷ digits)) x (a≥1→div2-10ᵃ (length (y ∷ digits)) (s≤s z≤n)))
                                    div2-x∷y∷digits



div-rule-2-inv : ∀ (decimal : List ℕ)
               → (l>0 : length decimal > 0)
               → (d<10 : all (_<ᵇ 10) decimal ≡ true)
               → Div2 (toℕ decimal l>0 d<10)
               → Div2 (last decimal l>0 d<10)
div-rule-2-inv (x ∷ []) _ _ div2-x = div2-x
div-rule-2-inv (x ∷ y ∷ decimal) (s≤s z≤n) d<10 div2-x∷y∷decimal =
               div-rule-2-inv (y ∷ decimal)
                              (s≤s z≤n)
                              (all→rest (_<ᵇ 10) x (y ∷ decimal) d<10)
                              (lemma-div2-cons-inv x
                                                   (all→head (_<ᵇ 10) x (y ∷ decimal) d<10)
                                                   (y ∷ decimal)
                                                   (s≤s z≤n)
                                                   (all→rest (_<ᵇ 10) x (y ∷ decimal) d<10)
                                                   div2-x∷y∷decimal)



alg-div-rule-2 : ∀ (a b : ℕ) → Div2 b → Div2 (10 * a + b)
alg-div-rule-2 a b div2-b = d2a→d2b→d2[a+b] (10 * a) b (d2a→d2[a*b] 10 a div2-10) div2-b



{-
--without div-rule-2
_ : Div2 6 → Div2 123456
_ = λ div2-6 → {!!}
--as a demo, try doing the above using C-c C-a after putting "-t 60" or "-t 300" in the placeholder
-}

--with div-rule-2
_ : Div2 6 → Div2 123456
_ = λ div2-6 → alg-div-rule-2 12345 6 div2-6



alg-div-rule-2-inv : ∀ (a b : ℕ) → Div2 (10 * a + b) → Div2 b
alg-div-rule-2-inv a b div2-10a+b = d2a→d2[a+b]→d2b (10 * a) b (d2a→d2[a*b] 10 a div2-10) div2-10a+b



_ : Div2 123456 → Div2 6
_ = λ div2-123456 → alg-div-rule-2-inv 12345 6 div2-123456
