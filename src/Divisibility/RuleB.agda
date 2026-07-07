{-
Proofs around a generalized sum of digits based Divisibility Rule
- these proofs prove that a positional number in base 'b' is divisible by 'b ∸ 1'
  if and only if its sum of digits is divisible by 'b ∸ 1'

Notes:
1. ignores the length constraint for simplicity
   for example, an empty list is treated as a zero
2. fromℕ-solver uses a dummy counter parameter to satisfy the termination checker
-}



module Divisibility.RuleB where



open import Data.Nat using (ℕ; zero; suc; _>_; _+_; _*_; _≥_; _∸_; _≤_; z≤n; s≤s; _^_; _<ᵇ_; _≱_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-comm; *-comm; *-distribˡ-+; +-∸-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; _≢_)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all)
open import Utilities using (all→rest)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)



data Div (d : ℕ) (p : d > 0) : ℕ → Set where
  dz : Div d p zero
  ds : ∀ {n : ℕ} → Div d p n → Div d p (d + n)



da→db→d[a+b] : ∀ {d a b : ℕ} → (p : d > 0) → Div d p a → Div d p b → Div d p (a + b)
da→db→d[a+b] {d} {.(zero)} {b} p dz db = db
da→db→d[a+b] {d} {.(d + n)} {b} p (ds {n} da) db = subst (Div d p) (sym (+-assoc d n b)) (ds (da→db→d[a+b] p da db))



db→d[a*b] : ∀ {d a b : ℕ} → (p : d > 0) → Div d p b → Div d p (a * b)
db→d[a*b] {d} {zero} {b} p db = dz
db→d[a*b] {d} {suc a} {b} p db = da→db→d[a+b] p db (db→d[a*b] {d} {a} {b} p db)

da→d[a*b] : ∀ {d a b : ℕ} → (p : d > 0) → Div d p a → Div d p (a * b)
da→d[a*b] {d} {a} {b} p da = subst (Div d p) (*-comm b a) (db→d[a*b] {d} {b} {a} p da)



a→da : ∀ {a : ℕ} → (p : a > 0) → Div a p a
a→da {a} p = subst (Div a p) (+-identityʳ a) (ds dz)



div-+-comm : ∀ {d a b : ℕ} → (p : d > 0) → Div d p (a + b) → Div d p (b + a)
div-+-comm {d} {a} {b} p div-a+b = subst (Div d p) (+-comm a b) div-a+b



a≥b→a≡b+[a∸b] : ∀ (a b : ℕ) → a ≥ b → a ≡ b + (a ∸ b)
a≥b→a≡b+[a∸b] _ zero _ = refl
a≥b→a≡b+[a∸b] (suc a) (suc b) (s≤s a≥b) = cong suc (a≥b→a≡b+[a∸b] a b a≥b)



d[a∸b]→db→da : ∀ {d a b : ℕ} → (p : d > 0) → a ≥ b → Div d p (a ∸ b) → Div d p b → Div d p a
d[a∸b]→db→da {d} {a} {b} p a≥b d[a∸b] db = subst (Div d p) (sym (a≥b→a≡b+[a∸b] a b a≥b)) (da→db→d[a+b] p db d[a∸b])



d>0→0≱[d+n] : ∀ {d n : ℕ} → d > 0 → 0 ≱ (d + n)
d>0→0≱[d+n] {zero} {n} () 0>[d+n]

sa≥sb→a≥b : ∀ {a b : ℕ} → suc a ≥ suc b → a ≥ b
sa≥sb→a≥b (s≤s a≥b) = a≥b

[d+a]≥[d+b]→a≥b : ∀ {a b : ℕ} (d : ℕ) → d + a ≥ d + b → a ≥ b
[d+a]≥[d+b]→a≥b zero a≥b = a≥b
[d+a]≥[d+b]→a≥b (suc d) [d+a]≥[d+b] = [d+a]≥[d+b]→a≥b d (sa≥sb→a≥b [d+a]≥[d+b])

a≥b→[d+a]-[d+b]≡a+b : ∀ {a b : ℕ} (d : ℕ) → a ≥ b → d + a ∸ (d + b) ≡ a ∸ b
a≥b→[d+a]-[d+b]≡a+b zero a≥b = refl
a≥b→[d+a]-[d+b]≡a+b (suc d) a≥b = a≥b→[d+a]-[d+b]≡a+b d a≥b

da→db→d[a∸b] : ∀ {d a b : ℕ} → (p : d > 0) → a ≥ b → Div d p a → Div d p b → Div d p (a ∸ b)
da→db→d[a∸b] {d} {.(zero)} {.(zero)} p 0≥0 dz dz = dz
da→db→d[a∸b] {d} {.(zero)} {.(d + n)} d>0 0≥[d+n] dz (ds {n} dn) = ⊥-elim (d>0→0≱[d+n] d>0 0≥[d+n])
da→db→d[a∸b] {d} {.(d + n)} {.(zero)} p [d+n]≥0 (ds {n} dn) dz = ds dn
da→db→d[a∸b] {d} {.(d + a')} {.(d + b')} p d+a'≥d+b' (ds {a'} da') (ds {b'} db') =
             subst (Div d p)
                   (sym (a≥b→[d+a]-[d+b]≡a+b d ([d+a]≥[d+b]→a≥b d d+a'≥d+b')))
                   (da→db→d[a∸b] p ([d+a]≥[d+b]→a≥b d d+a'≥d+b') da' db')



a>0→[a+b]≢0 : ∀ {a b : ℕ} → a > 0 → a + b ≢ 0
a>0→[a+b]≢0 (s≤s x) ()

sa≡sb→a≡b : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
sa≡sb→a≡b refl = refl

a+b≡a+c→b≡c : ∀ (a b c : ℕ) → a + b ≡ a + c → b ≡ c
a+b≡a+c→b≡c zero b c 0+b≡0+c = 0+b≡0+c
a+b≡a+c→b≡c (suc a) b c a+b≡a+c = a+b≡a+c→b≡c a b c (sa≡sb→a≡b a+b≡a+c)

lemma-match-type-computation : ∀ {d n m : ℕ} (p : d > 0) → Div d p m → m ≡ d + n → Div d p n
lemma-match-type-computation p dz 0≡d+n = ⊥-elim (a>0→[a+b]≢0 p (sym 0≡d+n))
lemma-match-type-computation {d} {n} {.(d + k)} p (ds {k} dm) d+k≡d+n = subst (Div d p) (a+b≡a+c→b≡c d k n d+k≡d+n) dm

--saw a hint which involved +-cancelˡ-≡ but the hint itself was mostly unclear to me
--except that Agda couldn't see that the following was true
--hence required an external helper with Div d p m where m ≡ d + a
--also, the hint itself was not correct, but eventually got it working via the lemmas above
ds-da→da : ∀ {d a : ℕ} → (p : d > 0) → Div d p (d + a) → Div d p a
ds-da→da {d} {a} p d[d+a] = lemma-match-type-computation p d[d+a] refl

da→d[a+b]→db : ∀ {d a b : ℕ} → (p : d > 0) → Div d p a → Div d p (a + b) → Div d p b
da→d[a+b]→db {d} {.(zero)} {b} p dz d[0+b] = d[0+b]
da→d[a+b]→db {d} {.(d + n)} {b} p (ds {n} dn) d[a+b] = da→d[a+b]→db p dn (ds-da→da p (subst (Div d p) (+-assoc d n b) d[a+b]))



a≥b→a≡[a∸b]+b : ∀ (a b : ℕ) → a ≥ b → a ≡ (a ∸ b) + b
a≥b→a≡[a∸b]+b a b a≥b = subst (_≡_ a) (+-comm b (a ∸ b)) (a≥b→a≡b+[a∸b] a b a≥b)

d[a∸b]→da→db : ∀ {d a b : ℕ} → (p : d > 0) → a ≥ b → Div d p (a ∸ b) → Div d p a → Div d p b
d[a∸b]→da→db {d} {a} {b} p a≥b d[a∸b] da = da→d[a+b]→db p d[a∸b] (subst (Div d p) (a≥b→a≡[a∸b]+b a b a≥b) da)



a≤b→a≤b+c : ∀ (a b c : ℕ) → a ≤ b → a ≤ b + c
a≤b→a≤b+c zero b c z≤n = z≤n
a≤b→a≤b+c (suc a) (suc b) c (s≤s a≤b) = s≤s (a≤b→a≤b+c a b c a≤b)



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



b>1→b∸1>0 : ∀ (b : ℕ) → b > 1 → b ∸ 1 > 0
b>1→b∸1>0 (suc b) (s≤s b>0) = b>0



b>1→b≥1 : ∀ b → b > 1 → b ≥ 1
b>1→b≥1 zero ()
b>1→b≥1 (suc b) (s≤s b>0) = s≤s z≤n



--b is base
div-b∸1-bᵃ∸1 : ∀ (a b : ℕ)
             → (b>1 : b > 1)
             → Div (b ∸ 1) (b>1→b∸1>0 b b>1) (b ^ a ∸ 1)
div-b∸1-bᵃ∸1 a b b>1 with b∸1-divides-bᵃ∸1 a b (b>1→b≥1 b b>1)
...                     | q , bᵃ∸1≡q*[b∸1]
                        = subst (Div (b ∸ 1) (b>1→b∸1>0 b b>1))
                                (sym bᵃ∸1≡q*[b∸1])
                                (db→d[a*b] {b ∸ 1} {q} {b ∸ 1} (b>1→b∸1>0 b b>1) (a→da (b>1→b∸1>0 b b>1)))



--b is base
sodᵇ : (b : ℕ)
     → (b>1 : b > 1)
     → (digits : List ℕ)
     → (all (_<ᵇ b) digits ≡ true)
     → ℕ
sodᵇ b b>1 [] _ = 0
sodᵇ b b>1 (x ∷ digits) valid = x + (sodᵇ b b>1 digits (all→rest (_<ᵇ b) x digits valid))



--b is base
toℕᵇ : (b : ℕ)
     → (b>1 : b > 1)
     → (digits : List ℕ)
     → (all (_<ᵇ b) digits ≡ true)
     → ℕ
toℕᵇ b b>1 [] _ = 0
toℕᵇ b b>1 (x ∷ digits) valid = ((b ^ (length digits)) * x)
                              + toℕᵇ b b>1 digits (all→rest (_<ᵇ b) x digits valid)

_ : toℕᵇ 10 (s≤s (s≤s z≤n)) [] refl ≡ 0
_ = refl

_ : toℕᵇ 10 (s≤s (s≤s z≤n)) (0 ∷ []) refl ≡ 0
_ = refl

_ : toℕᵇ 10 (s≤s (s≤s z≤n)) (0 ∷ 1 ∷ []) refl ≡ 1
_ = refl

_ : toℕᵇ 10 (s≤s (s≤s z≤n)) (1 ∷ 2 ∷ 3 ∷ []) refl ≡ 123
_ = refl

_ : toℕᵇ 2 (s≤s (s≤s z≤n)) (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []) refl ≡ 65
_ = refl

_ : toℕᵇ 16 (s≤s (s≤s z≤n)) (4 ∷ 1 ∷ []) refl ≡ 65
_ = refl

_ : toℕᵇ 11 (s≤s (s≤s z≤n)) (9 ∷ 1 ∷ []) refl ≡ 100
_ = refl



a≤a : ∀ (a : ℕ) → a ≤ a
a≤a zero = z≤n
a≤a (suc a) = s≤s (a≤a a)



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



lemma-+∸+≡∸+∸ : ∀ (a b c d : ℕ)
              → c ≤ a
              → d ≤ b
              → (a + b) ∸ (c + d) ≡ (a ∸ c) + (b ∸ d)
lemma-+∸+≡∸+∸ a b zero zero _ _ = refl
lemma-+∸+≡∸+∸ a (suc b) zero (suc d) z≤n (s≤s d≤b)
              rewrite +-comm a (suc b)
                    | +-comm b a
                    | +-∸-assoc a d≤b
                    = refl
lemma-+∸+≡∸+∸ a b (suc c) zero sc≤a z≤n
              rewrite +-identityʳ c
                    | +-comm (a ∸ suc c) b
                    | sym (+-∸-assoc b sc≤a)
                    | +-comm b a
                    = refl
lemma-+∸+≡∸+∸ (suc a) (suc b) (suc c) (suc d) (s≤s c≤a) (s≤s d≤b)
              rewrite +-comm c (suc d)
                    | +-comm d c
                    | a+sb∸sc≡a+b∸c a b (c + d)
                    | lemma-+∸+≡∸+∸ a b c d c≤a d≤b
                    = refl



b≥1→a≤b*a : ∀ (a b : ℕ) → b ≥ 1 → a ≤ b * a
b≥1→a≤b*a a (suc b) (s≤s z≤n) = a≤b→a≤b+c a a (b * a) (a≤a a)



a≤c→b≤d→a+b≤c+d : ∀ (a b c d : ℕ) → a ≤ c → b ≤ d → a + b ≤ c + d
a≤c→b≤d→a+b≤c+d zero b zero d _ b≤d = b≤d
a≤c→b≤d→a+b≤c+d zero b (suc c) d _ b≤d rewrite +-comm (suc c) d = a≤b→a≤b+c b d (suc c) b≤d
a≤c→b≤d→a+b≤c+d (suc a) b (suc c) d (s≤s a≤c) b≤d = s≤s (a≤c→b≤d→a+b≤c+d a b c d a≤c b≤d)



sodᵇ≤toℕᵇ : ∀ (b : ℕ)
            → (b>1 : b > 1)
            → (xs : List ℕ)
            → (<b : all (_<ᵇ b) xs ≡ true)
            → sodᵇ b b>1 xs <b ≤ toℕᵇ b b>1 xs <b
sodᵇ≤toℕᵇ b b>1 [] <b = z≤n
sodᵇ≤toℕᵇ b b>1 (x ∷ xs) <b =
  let
    l-xs = length xs
    <b-xs = all→rest (_<ᵇ b) x xs <b
  in
    a≤c→b≤d→a+b≤c+d x
                    (sodᵇ b b>1 xs <b-xs)
                    ((b ^ l-xs) * x)
                    (toℕᵇ b b>1 xs <b-xs)
                    (b≥1→a≤b*a x (b ^ l-xs) (b≥1→bᵃ≥1 b l-xs (b>1→b≥1 b b>1)))
                    (sodᵇ≤toℕᵇ b b>1 xs <b-xs)



toℕᵇ∸sodᵇ-x∷xs : ∀ (b : ℕ)
               → (b>1 : b > 1)
               → (x : ℕ)
               → (xs : List ℕ)
               → (d<b : all (_<ᵇ b) (x ∷ xs) ≡ true)
               → let <-xs = all→rest (_<ᵇ b) x xs d<b in
                 (toℕᵇ b b>1 (x ∷ xs) d<b) ∸ (sodᵇ b b>1 (x ∷ xs) d<b)
                 ≡ (x * ((b ^ (length xs)) ∸ 1)) + ((toℕᵇ b b>1 xs <-xs) ∸ (sodᵇ b b>1 xs <-xs))
toℕᵇ∸sodᵇ-x∷xs b b>1 x xs d<b =
  let
    l-xs = (length xs)
    <-xs = all→rest (_<ᵇ b) x xs d<b
    toℕᵇ-xs = (toℕᵇ b b>1 xs <-xs)
    sodᵇ-xs = (sodᵇ b b>1 xs <-xs)
  in
    begin
      toℕᵇ b b>1 (x ∷ xs) d<b ∸ sodᵇ b b>1 (x ∷ xs) d<b
    ≡⟨⟩
      (((b ^ l-xs) * x) + toℕᵇ-xs) ∸ (x + sodᵇ-xs)
    ≡⟨ lemma-+∸+≡∸+∸ ((b ^ l-xs) * x)
                     toℕᵇ-xs
                     x
                     sodᵇ-xs
                     (b≥1→a≤b*a x (b ^ l-xs) (b≥1→bᵃ≥1 b l-xs (b>1→b≥1 b b>1)))
                     (sodᵇ≤toℕᵇ b b>1 xs <-xs) ⟩
      (((b ^ l-xs) * x) ∸ x) + (toℕᵇ-xs ∸ sodᵇ-xs)
    ≡⟨ cong (_+ (toℕᵇ-xs ∸ sodᵇ-xs)) (a*b∸b≡b*[a∸1] (b ^ l-xs) x) ⟩
      x * (b ^ l-xs ∸ 1) + (toℕᵇ-xs ∸ sodᵇ-xs)
    ∎



b∸1-divides-[toℕᵇ∸sodᵇ] : ∀ (b : ℕ)
                        → (b>1 : b > 1)
                        → (digits : List ℕ)
                        → (d<b : all (_<ᵇ b) digits ≡ true)
                        → Div (b ∸ 1) (b>1→b∸1>0 b b>1) ((toℕᵇ b b>1 digits d<b) ∸ (sodᵇ b b>1 digits d<b))
b∸1-divides-[toℕᵇ∸sodᵇ] b b>1 [] d<b = dz
b∸1-divides-[toℕᵇ∸sodᵇ] b b>1 (x ∷ digits) d<b =
  let
    <-digits = all→rest (_<ᵇ b) x digits d<b
  in
    subst (Div (b ∸ 1) (b>1→b∸1>0 b b>1))
          (sym (toℕᵇ∸sodᵇ-x∷xs b b>1 x digits d<b))
          (da→db→d[a+b] (b>1→b∸1>0 b b>1)
                        (db→d[a*b] {b ∸ 1} {x} {b ^ length digits ∸ 1} (b>1→b∸1>0 b b>1) (div-b∸1-bᵃ∸1 (length digits) b b>1))
                        (b∸1-divides-[toℕᵇ∸sodᵇ] b b>1 digits <-digits))



div-ruleᵇ : ∀ (b : ℕ)
            → (b>1 : b > 1)
            → (digits : List ℕ)
            → (d<b : all (_<ᵇ b) digits ≡ true)
            → Div (b ∸ 1) (b>1→b∸1>0 b b>1) (sodᵇ b b>1 digits d<b)
            → Div (b ∸ 1) (b>1→b∸1>0 b b>1) (toℕᵇ b b>1 digits d<b)
div-ruleᵇ b b>1 digits d<b div-sod = d[a∸b]→db→da (b>1→b∸1>0 b b>1)
                                                  (sodᵇ≤toℕᵇ b b>1 digits d<b)
                                                  (b∸1-divides-[toℕᵇ∸sodᵇ] b b>1 digits d<b)
                                                  div-sod



--based on div-helper in Agda.Builtin.Nat
divmod-solver : (a : ℕ) → (b : ℕ) → (q : ℕ) → (r : ℕ) → ℕ × ℕ
divmod-solver zero b q r = q , b ∸ r
divmod-solver (suc a) b q zero = divmod-solver a b (suc q) b
divmod-solver (suc a) b q (suc r) = divmod-solver a b q r

divmod : (a : ℕ) → (b : ℕ) → (b>0 : b > 0) → ℕ × ℕ
divmod a (suc b) b>0 = divmod-solver a b zero b



--b is base
fromℕ-solverᵇ : (b : ℕ)
              → (b>1 : b > 1)
              → ℕ
              → (counter : ℕ)
              → (acc : List ℕ)
              → List ℕ
fromℕ-solverᵇ b b>1 zero counter acc = acc
fromℕ-solverᵇ b b>1 (suc n) zero acc = acc --will never be here, counter is a dummy parameter to appease the termination checker
fromℕ-solverᵇ b b>1 (suc n) (suc counter) acc = let qr = divmod (suc n) b (b>1→b≥1 b b>1)
                                                in fromℕ-solverᵇ b b>1 (proj₁ qr) counter ((proj₂ qr) ∷ acc)

fromℕᵇ : (b : ℕ)
       → (b>1 : b > 1)
       → ℕ
       → List ℕ
fromℕᵇ b b>1 zero = 0 ∷ []
fromℕᵇ b b>1 (suc n) = fromℕ-solverᵇ b b>1 (suc n) (suc n) []



lemma-from-0 : ∀ {b : ℕ} → {b>1 : b > 1} → fromℕᵇ b b>1 0 ≡ 0 ∷ []
lemma-from-0 = refl

_ : fromℕᵇ 2 (s≤s (s≤s z≤n)) 1 ≡ 1 ∷ []
_ = refl

_ : fromℕᵇ 10 (s≤s (s≤s z≤n)) 1 ≡ 1 ∷ []
_ = refl

_ : fromℕᵇ 10 (s≤s (s≤s z≤n)) 123 ≡ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : fromℕᵇ 2 (s≤s (s≤s z≤n)) 11 ≡ 1 ∷ 0 ∷ 1 ∷ 1 ∷ []
_ = refl

_ : fromℕᵇ 3 (s≤s (s≤s z≤n)) 11  ≡ 1 ∷ 0 ∷ 2 ∷ []
_ = refl



digits-large-num : List ℕ
digits-large-num = 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

{-
_ : Div 9 (s≤s z≤n) (toℕᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl)
_ = {!!}
--this will likely take an impractically long amount of time and large amount of memory
-}

_ : Div 9 (s≤s z≤n) (toℕᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl)
_ = div-ruleᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl (ds (ds (ds (ds (ds dz)))))

_ : Div 9 (s≤s z≤n) (toℕᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl)
_ = div-ruleᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl
    (div-ruleᵇ 10 (s≤s (s≤s z≤n)) (fromℕᵇ 10 (s≤s (s≤s z≤n)) (sodᵇ 10 (s≤s (s≤s z≤n)) digits-large-num refl)) refl (ds dz))



div-ruleᵇ-inv : ∀ (b : ℕ)
              → (b>1 : b > 1)
              → (digits : List ℕ)
              → (d<b : all (_<ᵇ b) digits ≡ true)
              → Div (b ∸ 1) (b>1→b∸1>0 b b>1) (toℕᵇ b b>1 digits d<b)
              → Div (b ∸ 1) (b>1→b∸1>0 b b>1) (sodᵇ b b>1 digits d<b)
div-ruleᵇ-inv b b>1 digits d<b div-digits = d[a∸b]→da→db (b>1→b∸1>0 b b>1)
                                                         (sodᵇ≤toℕᵇ b b>1 digits d<b)
                                                         (b∸1-divides-[toℕᵇ∸sodᵇ] b b>1 digits d<b)
                                                         div-digits



large-num₁₀ : List ℕ
large-num₁₀ = 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []

Div3 = Div 3 (s≤s z≤n)
Div9 = Div 9 (s≤s z≤n)
toℕ₁₀ = toℕᵇ 10 (s≤s (s≤s z≤n))
fromℕ₁₀ = fromℕᵇ 10 (s≤s (s≤s z≤n))
sod₁₀ = sodᵇ 10 (s≤s (s≤s z≤n))
div-rule₁₀ = div-ruleᵇ 10 (s≤s (s≤s z≤n))

div9→div3 : ∀ (n : ℕ) → Div9 n → Div3 n
div9→div3 zero _ = dz
div9→div3 (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) (ds div9-n) = ds (ds (ds (div9→div3 n div9-n)))

_ : Div3 (toℕ₁₀ large-num₁₀ refl)
_ = div9→div3 (toℕ₁₀ large-num₁₀ refl) (div-rule₁₀ large-num₁₀ refl (ds (ds (ds (ds (ds dz))))))

_ : Div3 (toℕ₁₀ large-num₁₀ refl)
_ = div9→div3 (toℕ₁₀ large-num₁₀ refl)
    (div-rule₁₀ large-num₁₀ refl (div-rule₁₀ (fromℕ₁₀ (sod₁₀ large-num₁₀ refl)) refl (ds dz)))



{-
_ : Div3 12345
_ = {!!}
--comes up with a long string of ds (4115 of them) and a single dz but takes ~30 seconds with -t 60
-}

_ : Div3 12345
_ = ds (ds (div9→div3 12339 (div-rule₁₀ (fromℕ₁₀ 12339) refl (ds (ds dz)))))

--but for numbers divisible by 3 but not by 9, it can also be done by converting the number to base 4
fromℕ₄ = fromℕᵇ 4 (s≤s (s≤s z≤n))
div-rule₄ = div-ruleᵇ 4 (s≤s (s≤s z≤n))

_ : Div3 12345
_ = div-rule₄ (fromℕ₄ 12345) refl (ds (ds (ds dz)))
