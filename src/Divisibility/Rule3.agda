{-
Proofs around the Divisibility Rule of 3 on base-10 list encoded naturals
  lines 361 and 421

Unlike Divisibility.Rule2, this one ignores the length constraint for simplicity
for example, an empty list is treated as a zero

fromℕ-solver uses a dummy counter parameter to satisfy the termination checker
-}



module Divisibility.Rule3 where



open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≥_; _∸_; _≤_; z≤n; s≤s; _<ᵇ_; _^_; _>_)
open import Data.Nat.Properties using (+-comm; *-comm; +-assoc; +-∸-assoc; +-identityʳ; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all)
open import Utilities using (all→rest)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)



data Div3 : ℕ → Set where
  d3z : Div3 0
  d3s : ∀ {n : ℕ} → Div3 n → Div3 (suc (suc (suc n)))



d3a→d3b→d3[a+b] : ∀ (a b : ℕ) → Div3 a → Div3 b → Div3 (a + b)
d3a→d3b→d3[a+b] zero b d3z div3-b = div3-b
d3a→d3b→d3[a+b] (suc (suc (suc a))) b (d3s div3-a) div3-b = d3s (d3a→d3b→d3[a+b] a b div3-a div3-b)



d3[a+b]→d3a→d3b : ∀ (a b : ℕ) → Div3 (a + b) → Div3 a → Div3 b
d3[a+b]→d3a→d3b zero b div3-0+b div3-0 = div3-0+b
d3[a+b]→d3a→d3b (suc (suc (suc a))) b (d3s div3-a+b) (d3s div3-a) = d3[a+b]→d3a→d3b a b div3-a+b div3-a



div3-+-comm : ∀ (a b : ℕ) → Div3 (a + b) → Div3 (b + a)
div3-+-comm a b div3-a+b rewrite +-comm a b = div3-a+b



d3b→d3[a*b] : ∀ (a b : ℕ) → Div3 b → Div3 (a * b)
d3b→d3[a*b] zero b div3-b = d3z
d3b→d3[a*b] (suc a) b div3-b = d3a→d3b→d3[a+b] b (a * b) div3-b (d3b→d3[a*b] a b div3-b)



a≥b→a≡b+[a∸b] : ∀ (a b : ℕ) → a ≥ b → a ≡ b + (a ∸ b)
a≥b→a≡b+[a∸b] zero zero z≤n = refl
a≥b→a≡b+[a∸b] zero (suc b) ()
a≥b→a≡b+[a∸b] (suc a) zero z≤n = refl
a≥b→a≡b+[a∸b] (suc a) (suc b) (s≤s x) = cong suc (a≥b→a≡b+[a∸b] a b x)



d3[a∸b]→d3b→d3a : ∀ (a b : ℕ) → a ≥ b → Div3 (a ∸ b) → Div3 b → Div3 a
d3[a∸b]→d3b→d3a a b a≥b div3-[a∸b] div3-b = subst Div3
                                                  (sym (a≥b→a≡b+[a∸b] a b a≥b))
                                                  (d3a→d3b→d3[a+b] b (a ∸ b) div3-b div3-[a∸b])



d3[a∸b]→d3a→d3b : ∀ (a b : ℕ) → a ≥ b → Div3 (a ∸ b) → Div3 a → Div3 b
d3[a∸b]→d3a→d3b a b a≥b div3-[a∸b] div3-a =
                d3[a+b]→d3a→d3b (a ∸ b)
                                b
                                (div3-+-comm b (a ∸ b) (subst Div3 (a≥b→a≡b+[a∸b] a b a≥b) div3-a))
                                div3-[a∸b]



sodᵇ : (base : ℕ) → (digits : List ℕ) → (all (_<ᵇ base) digits ≡ true) → ℕ
sodᵇ base [] _ = 0
sodᵇ base (x ∷ digits) valid = x + (sodᵇ base digits (all→rest (_<ᵇ base) x digits valid))



toℕᵇ : (base : ℕ) → (digits : List ℕ) → (all (_<ᵇ base) digits ≡ true) → ℕ
toℕᵇ base [] _ = 0
toℕᵇ base (x ∷ digits) valid = ((base ^ (length digits)) * x)
                             + toℕᵇ base digits (all→rest (_<ᵇ base) x digits valid)

_ : toℕᵇ 10 [] refl ≡ 0
_ = refl

_ : toℕᵇ 10 (0 ∷ []) refl ≡ 0
_ = refl

_ : toℕᵇ 10 (0 ∷ 1 ∷ []) refl ≡ 1
_ = refl

_ : toℕᵇ 10 (1 ∷ 2 ∷ 3 ∷ []) refl ≡ 123
_ = refl

_ : toℕᵇ 2 (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []) refl ≡ 65
_ = refl



--based on div-helper in Agda.Builtin.Nat
divmod-solver : (a : ℕ) → (b : ℕ) → (q : ℕ) → (r : ℕ) → ℕ × ℕ
divmod-solver zero b q r = q , b ∸ r
divmod-solver (suc a) b q zero = divmod-solver a b (suc q) b
divmod-solver (suc a) b q (suc r) = divmod-solver a b q r

divmod : (a : ℕ) → (b : ℕ) → {b > zero} → ℕ × ℕ
divmod a (suc b) = divmod-solver a b zero b



fromℕ-solver : ℕ → ℕ → List ℕ → List ℕ
fromℕ-solver zero counter acc = acc
fromℕ-solver (suc n) zero acc = acc --will never be here, counter is a dummy parameter to appease the termination checker
fromℕ-solver (suc n) (suc counter) acc = let qr = divmod (suc n) 10 { s≤s z≤n }
                                         in fromℕ-solver (proj₁ qr) counter ((proj₂ qr) ∷ acc)

fromℕ : ℕ → List ℕ
fromℕ zero = 0 ∷ []
fromℕ (suc n) = fromℕ-solver (suc n) (suc n) []

_ : fromℕ 0 ≡ 0 ∷ []
_ = refl

_ : fromℕ 1 ≡ 1 ∷ []
_ = refl

_ : fromℕ 123 ≡ 1 ∷ 2 ∷ 3 ∷ []
_ = refl



a≤b→a≤b+c : ∀ (a b c : ℕ) → a ≤ b → a ≤ b + c
a≤b→a≤b+c zero b c z≤n = z≤n
a≤b→a≤b+c (suc a) (suc b) c (s≤s a≤b) = s≤s (a≤b→a≤b+c a b c a≤b)



a≤c→b≤d→a+b≤c+d : ∀ (a b c d : ℕ) → a ≤ c → b ≤ d → a + b ≤ c + d
a≤c→b≤d→a+b≤c+d zero b zero d _ b≤d = b≤d
a≤c→b≤d→a+b≤c+d zero b (suc c) d _ b≤d rewrite +-comm (suc c) d = a≤b→a≤b+c b d (suc c) b≤d
a≤c→b≤d→a+b≤c+d (suc a) b (suc c) d (s≤s a≤c) b≤d = s≤s (a≤c→b≤d→a+b≤c+d a b c d a≤c b≤d)



a≤a : ∀ (a : ℕ) → a ≤ a
a≤a zero = z≤n
a≤a (suc a) = s≤s (a≤a a)



b≥1→a≤b*a : ∀ (a b : ℕ) → b ≥ 1 → a ≤ b * a
b≥1→a≤b*a a (suc b) (s≤s z≤n) = a≤b→a≤b+c a a (b * a) (a≤a a)



c≥1→a≤b→a≤b*c : ∀ (a b c : ℕ) → c ≥ 1 → a ≤ b → a ≤ b * c
c≥1→a≤b→a≤b*c zero zero (suc c) (s≤s z≤n) z≤n = z≤n
c≥1→a≤b→a≤b*c zero (suc b) (suc c) (s≤s z≤n) z≤n = z≤n
c≥1→a≤b→a≤b*c (suc a) (suc b) (suc c) (s≤s z≤n) (s≤s a≤b)
              rewrite *-comm b (suc c)
                    | sym (+-assoc c b (c * b))
                    | +-comm c b
                    | +-assoc b c (c * b)
                    = s≤s (a≤b→a≤b+c a b (c + c * b) a≤b)



b≥1→bᵃ≥1 : ∀ (b a : ℕ) → b ≥ 1 → (b ^ a) ≥ 1
b≥1→bᵃ≥1 b zero _ = s≤s z≤n
b≥1→bᵃ≥1 b (suc a) b≥1 rewrite *-comm b (b ^ a) = c≥1→a≤b→a≤b*c 1 (b ^ a) b b≥1 (b≥1→bᵃ≥1 b a b≥1)



sodᵇ≤toℕᵇ : ∀ (b : ℕ)
            → b ≥ 1
            → (xs : List ℕ)
            → (<b : all (_<ᵇ b) xs ≡ true)
            → sodᵇ b xs <b ≤ toℕᵇ b xs <b
sodᵇ≤toℕᵇ b b≥1 [] <b = z≤n
sodᵇ≤toℕᵇ b b≥1 (x ∷ xs) <b =
  let
    l-xs = length xs
    <b-xs = all→rest (_<ᵇ b) x xs <b
  in
    a≤c→b≤d→a+b≤c+d x
                    (sodᵇ b xs <b-xs)
                    ((b ^ l-xs) * x)
                    (toℕᵇ b xs <b-xs)
                    (b≥1→a≤b*a x (b ^ l-xs) (b≥1→bᵃ≥1 b l-xs b≥1))
                    (sodᵇ≤toℕᵇ b b≥1 xs <b-xs)



n∸n≡0 : ∀ (n : ℕ) → n ∸ n ≡ 0
n∸n≡0 zero = refl
n∸n≡0 (suc n) = n∸n≡0 n



a*b∸b≡b*[a∸1] : ∀ (a b : ℕ) → a * b ∸ b ≡ b * (a ∸ 1)
a*b∸b≡b*[a∸1] zero zero = refl
a*b∸b≡b*[a∸1] zero (suc b) rewrite *-comm b 0 = refl
a*b∸b≡b*[a∸1] (suc a) zero rewrite *-comm a 0 = refl
a*b∸b≡b*[a∸1] (suc a) (suc b)
              rewrite +-comm b (a * suc b)
                    | +-∸-assoc (a * suc b) (a≤a b)
                    | n∸n≡0 b
                    | +-identityʳ (a * suc b)
                    | *-comm a (suc b)
                    = refl



a+sb∸sc≡a+b∸c : ∀ (a b c : ℕ) → a + suc b ∸ suc c ≡ a + b ∸ c
a+sb∸sc≡a+b∸c zero zero c = refl
a+sb∸sc≡a+b∸c zero (suc b) c = refl
a+sb∸sc≡a+b∸c (suc a) zero c rewrite +-identityʳ a | +-comm a 1 = refl
a+sb∸sc≡a+b∸c (suc a) (suc b) c rewrite +-comm a (suc (suc b)) | +-comm a (suc b) = refl



lemma-+∸+≡∸+∸ : ∀ (a b c d : ℕ) → c ≤ a → d ≤ b → (a + b) ∸ (c + d) ≡ (a ∸ c) + (b ∸ d)
lemma-+∸+≡∸+∸ a b zero zero _ _ = refl
lemma-+∸+≡∸+∸ a (suc b) zero (suc d) z≤n (s≤s d≤b)
              rewrite +-comm a (suc b)
                    | +-comm b a
                    | +-∸-assoc a d≤b = refl
lemma-+∸+≡∸+∸ a b (suc c) zero sc≤a z≤n
              rewrite +-identityʳ c
                    | +-comm (a ∸ suc c) b
                    | sym (+-∸-assoc b sc≤a)
                    | +-comm b a = refl
lemma-+∸+≡∸+∸ (suc a) (suc b) (suc c) (suc d) (s≤s c≤a) (s≤s d≤b)
              rewrite +-comm c (suc d)
                    | +-comm d c
                    | a+sb∸sc≡a+b∸c a b (c + d)
                    | lemma-+∸+≡∸+∸ a b c d c≤a d≤b = refl



toℕᵇ∸sodᵇ-x∷xs : ∀ (b : ℕ)
               → b ≥ 1
               → (x : ℕ)
               → (xs : List ℕ)
               → (d<b : all (_<ᵇ b) (x ∷ xs) ≡ true)
               → let <-xs = all→rest (_<ᵇ b) x xs d<b in
                 (toℕᵇ b (x ∷ xs) d<b) ∸ (sodᵇ b (x ∷ xs) d<b)
                 ≡ (x * ((b ^ (length xs)) ∸ 1)) + ((toℕᵇ b xs <-xs) ∸ (sodᵇ b xs <-xs))
toℕᵇ∸sodᵇ-x∷xs b b≥1 x xs d<b =
  let
    l-xs = (length xs)
    <-xs = all→rest (_<ᵇ b) x xs d<b
    toℕᵇ-xs = (toℕᵇ b xs <-xs)
    sodᵇ-xs = (sodᵇ b xs <-xs)
  in
    begin
      toℕᵇ b (x ∷ xs) d<b ∸ sodᵇ b (x ∷ xs) d<b
    ≡⟨⟩
      (((b ^ l-xs) * x) + toℕᵇ-xs) ∸ (x + sodᵇ-xs)
    ≡⟨ lemma-+∸+≡∸+∸ ((b ^ l-xs) * x) toℕᵇ-xs x sodᵇ-xs (b≥1→a≤b*a x (b ^ l-xs) (b≥1→bᵃ≥1 b l-xs b≥1)) (sodᵇ≤toℕᵇ b b≥1 xs <-xs) ⟩
      (((b ^ l-xs) * x) ∸ x) + (toℕᵇ-xs ∸ sodᵇ-xs)
    ≡⟨ cong (_+ (toℕᵇ-xs ∸ sodᵇ-xs)) (a*b∸b≡b*[a∸1] (b ^ l-xs) x) ⟩
      x * (b ^ l-xs ∸ 1) + (toℕᵇ-xs ∸ sodᵇ-xs)
    ∎



lemma-*-split : ∀ a b → a ≥ 1 → a * b ≡ b + (a ∸ 1) * b
lemma-*-split (suc a) b _ = refl

lemma-bᵃ∸1-suc : ∀ a b q → b ≥ 1 → b ^ a ∸ 1 ≡ q * (b ∸ 1) → b ^ (suc a) ∸ 1 ≡ (b ^ a + q) * (b ∸ 1)
lemma-bᵃ∸1-suc a b q b≥1 bᵃ∸1≡q[b∸1] =
  begin
    b ^ suc a ∸ 1
  ≡⟨ refl ⟩
    b * (b ^ a) ∸ 1
  ≡⟨ cong (_∸ 1) (lemma-*-split b (b ^ a) b≥1) ⟩
    (b ^ a) + ((b ∸ 1) * (b ^ a)) ∸ 1
  ≡⟨ cong (_∸ 1) (+-comm (b ^ a) ((b ∸ 1) * b ^ a)) ⟩
    ((b ∸ 1) * (b ^ a)) + (b ^ a) ∸ 1
  ≡⟨ +-∸-assoc ((b ∸ 1) * (b ^ a)) (b≥1→bᵃ≥1 b a b≥1) ⟩
    ((b ∸ 1) * (b ^ a)) + ((b ^ a) ∸ 1)
  ≡⟨ cong (((b ∸ 1) * (b ^ a)) +_) bᵃ∸1≡q[b∸1] ⟩
    ((b ∸ 1) * (b ^ a)) + (q * (b ∸ 1))
  ≡⟨ cong (((b ∸ 1) * (b ^ a)) +_) (*-comm q (b ∸ 1)) ⟩
    ((b ∸ 1) * (b ^ a)) + ((b ∸ 1) * q)
  ≡⟨ sym (*-distribˡ-+ (b ∸ 1) (b ^ a) q) ⟩
    (b ∸ 1) * ((b ^ a) + q)
  ≡⟨ *-comm (b ∸ 1) (b ^ a + q) ⟩
    (b ^ a + q) * (b ∸ 1)
  ∎

b∸1-divides-bᵃ∸1 : ∀ (a b : ℕ) → b ≥ 1 → ∃[ q ] ((b ^ a) ∸ 1 ≡ q * (b ∸ 1))
b∸1-divides-bᵃ∸1 zero b b≥1 = 0 , refl
b∸1-divides-bᵃ∸1 (suc a) b b≥1 =
                 let q , bᵃ∸1≡q[b∸1] = b∸1-divides-bᵃ∸1 a b b≥1
                 in (b ^ a) + q , lemma-bᵃ∸1-suc a b q b≥1 bᵃ∸1≡q[b∸1]
{-
from IH there is some q such that b ^ a ∸ 1 ≡ q * (b ∸ 1)
now, b ^ (suc a) ∸ 1
   = b * (b ^ a) ∸ 1
   = (b ^ a) + ((b ∸ 1) * (b ^ a)) ∸ 1
   = ((b ∸ 1) * (b ^ a)) + (b ^ a) ∸ 1
   = ((b ∸ 1) * (b ^ a)) + (b ^ a ∸ 1)
   = ((b ∸ 1) * (b ^ a)) + (q * (b ∸ 1)) from IH
   = ((b ∸ 1) * (b ^ a)) + ((b ∸ 1) * q)
   = (b ∸ 1) * ((b ^ a) + q)
   = ((b ^ a) + q) * (b ∸ 1)
which means (b ∸ 1) divides (b ^ (suc a) ∸ 1), hence proved
but to prove constructively we need a q' such that b ^ (suc a) ∸ 1 ≡ q' * (b ∸ 1)
so, q' = (((b ^ a) + q) * (b ∸ 1)) / (b ∸ 1)
       = (b ^ a) + q
       = ((q * (b ∸ 1)) + 1) + q from IH
       = qb ∸ q + 1 + q
       = qb + 1
so, we can use any of "(b ^ a) + q" or "qb + 1" as q'
-}



div9-10ᵃ∸1 : ∀ (a : ℕ) → ∃[ q ] (10 ^ a ∸ 1 ≡ q * 9)
div9-10ᵃ∸1 a = b∸1-divides-bᵃ∸1 a 10 (s≤s z≤n)

div3-n*9 : ∀ (n : ℕ) → Div3 (n * 9)
div3-n*9 zero = d3z
div3-n*9 (suc n) = d3s (d3s (d3s (div3-n*9 n)))

div3-10ᵃ∸1 : ∀ (a : ℕ) → Div3 ((10 ^ a) ∸ 1)
div3-10ᵃ∸1 a with div9-10ᵃ∸1 a
...             | q , 10ᵃ∸1≡q*9 = subst Div3 (sym 10ᵃ∸1≡q*9) (div3-n*9 q)



div3-decimal-[toℕᵇ∸sodᵇ] : ∀ (decimal : List ℕ)
                         → (d<10 : all (_<ᵇ 10) decimal ≡ true)
                         → Div3 ((toℕᵇ 10 decimal d<10) ∸ (sodᵇ 10 decimal d<10))
div3-decimal-[toℕᵇ∸sodᵇ] [] _ = d3z
div3-decimal-[toℕᵇ∸sodᵇ] (x ∷ decimal) d<10 =
  let
    <-xs = all→rest (_<ᵇ 10) x decimal d<10
  in
    subst Div3
              (sym (toℕᵇ∸sodᵇ-x∷xs 10 (s≤s z≤n) x decimal d<10))
              (d3a→d3b→d3[a+b] (x * ((10 ^ (length decimal)) ∸ 1))
                               ((toℕᵇ 10 decimal <-xs) ∸ sodᵇ 10 decimal <-xs)
                               (d3b→d3[a*b] x ((10 ^ (length decimal)) ∸ 1) (div3-10ᵃ∸1 (length decimal)))
                               (div3-decimal-[toℕᵇ∸sodᵇ] decimal <-xs))



div-rule-3 : ∀ (decimal : List ℕ)
             → (d<10 : all (_<ᵇ 10) decimal ≡ true)
             → Div3 (sodᵇ 10 decimal d<10)
             → Div3 (toℕᵇ 10 decimal d<10)
div-rule-3 decimal d<10 div3-sod = d3[a∸b]→d3b→d3a (toℕᵇ 10 decimal d<10)
                                                   (sodᵇ 10 decimal d<10)
                                                   (sodᵇ≤toℕᵇ 10 (s≤s z≤n) decimal d<10)
                                                   (div3-decimal-[toℕᵇ∸sodᵇ] decimal d<10)
                                                   div3-sod



digits30 : List ℕ
digits30 = 3 ∷ 0 ∷ []

_ : Div3 (toℕᵇ 10 digits30 refl)
_ = d3s (d3s (d3s (d3s (d3s (d3s (d3s (d3s (d3s (d3s d3z)))))))))

_ : Div3 (toℕᵇ 10 digits30 refl)
_ = div-rule-3 digits30 refl (d3s d3z)



digits132 : List ℕ
digits132 = 1 ∷ 3 ∷ 2 ∷ []

{-
_ : Div3 (toℕᵇ 10 digits132 refl)
_ = {!!}
--this used to take around a minute with -t 60 and C-c C-a in the placeholder
--but, the newer version of Agda (2.8) does this instantly
-}

_ : Div3 (toℕᵇ 10 digits132 refl)
_ = div-rule-3 digits132 refl (d3s (d3s d3z))



digits-large-num : List ℕ
digits-large-num = 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

{-
_ : Div3 (toℕᵇ 10 digits-large-num refl)
_ = {!!}
--this will likely take an impractically long amount of time and large amount of memory
-}

{-
_ : Div3 (toℕᵇ 10 digits-large-num refl)
_ = div-rule-3 digits-large-num refl {!!}
--this used to take a lot of time and memory without reaching the solution in ~3 minutes
--so, didn't wait for it to finish or run out of RAM
--but, the newer version of Agda (2.8) does this instantly
-}

_ : Div3 (toℕᵇ 10 digits-large-num refl)
_ = div-rule-3 digits-large-num refl (div-rule-3 (fromℕ (sodᵇ 10 digits-large-num refl)) refl (d3s (d3s (d3s d3z))))



div-rule-3-inv : ∀ (decimal : List ℕ)
               → (d<10 : all (_<ᵇ 10) decimal ≡ true)
               → Div3 (toℕᵇ 10 decimal d<10)
               → Div3 (sodᵇ 10 decimal d<10)
div-rule-3-inv decimal d<10 div3-decimal = d3[a∸b]→d3a→d3b (toℕᵇ 10 decimal d<10)
                                                           (sodᵇ 10 decimal d<10)
                                                           (sodᵇ≤toℕᵇ 10 (s≤s z≤n) decimal d<10)
                                                           (div3-decimal-[toℕᵇ∸sodᵇ] decimal d<10)
                                                           div3-decimal
