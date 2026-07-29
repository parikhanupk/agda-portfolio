module Puzzles.MO-Romania-1959-triangle where



open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s; _≥_; _<_; _>_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-comm; *-assoc; *-distribˡ-+; *-cancelˡ-≡)
open import Data.Nat.Properties using (m+n∸m≡n; *-distribˡ-∸)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; cong₂; _≢_; subst; subst₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat.Tactic.RingSolver using (solve)
open import Data.List using (List; []; _∷_)
open import Polynomials.Binomials using ([a∸b]²≡a²+b²∸2ab)
open import Naturals.Properties.EvenOdd using (Even; Odd; eo; es; os; even≢odd; even-or-odd)
open import Naturals.Properties.EvenOdd using (even+even≡even; even+odd≡odd; odd+even≡odd)
open import Naturals.Properties.EvenOdd using (*-evenˡ; *-odd-odd; even-a→a²≡4k²)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Utilities using (*-swap; a≤b→a≤b+c; a≤a)



{-
   construct a right triangle with given hypotenuse c such that
   the median drawn to the hypotenuse is the geometric mean of the two legs of the triangle
   suppose the legs have length a and b then
   - a² + b² = c² (right triangle)
   - 2 * m = c (right triangle)
   - m * m = a * b (median is the geometric mean of a and b)
   - also a can be assumed to be the equal-or-larger of the two legs, so a ≥ b
   - and since this is supposed to be a triangle a, b, c > 0
   now, 2m = c → 4m² = c² → 4ab = c²
   since, a² + b² = c²
        → a² + b² = 4ab
        → a² + b² + 2ab = 4ab + 2ab
        → (a + b)² = c² + c²/2
        → (a + b)² = 3/2 * c²
        → a + b = √(3/2) * c
   since, a² + b² = c²
        → a² + b² = 4ab
        → a² + b² - 2ab = 2ab
        → (a - b)² = c²/2
        → (a - b)² = 1/2 * c²
        → a - b = √(1/2) * c
   so, (a + b) + (a - b) = √(3/2) * c + √(1/2) * c
     → a = ((√3 + 1) / 2√2) * c
     → a = ((√2 * (√3 + 1)) / (√2 * 2√2)) * c
     → a = ((√6 + √2) / 4) * c
   and, a - b = √(1/2) * c
      → b = a - √(1/2) * c
      → b = ((√6 + √2) / 4) * c - √(1/2) * c
      → b = ((√6 + √2) / 4) * c - (2√2 / (2√2*√2)) * c
      → b = ((√6 + √2) / 4) * c - (2√2 / 4) * c
      → b = ((√6 + √2 - 2√2) / 4) * c
      → b = ((√6 - √2) / 4) * c
   so, a = ((√6 + √2) / 4) * c and b = ((√6 - √2) / 4) * c
   which results in proving the following 3 in context of naturals
   - note that proofs a and b are primarily about deriving a and b in terms of c
     so, a b c > 0 not used as there is no such triangle with a b c ∈ ℕ
   - but a b c > 0 used in proof c as it is to prove that a b c > 0 and a b c ∈ ℕ → no such triangle
a. 2 * ((a + b) * (a + b)) ≡ 3 * (c * c)
b. 2 * ((a ∸ b) * (a ∸ b)) ≡ (c * c) (where the equal-or-larger leg is a as mentioned above)
c. proving that the above derivations cannot result in such a triangle with all lengths in naturals
   that is, the problem's triangles can't have all side lengths in naturals
-}



proof-a : (a b c m : ℕ)
        → (a ≥ b)
        → (a * a + b * b ≡ c * c)
        → (2 * m ≡ c)
        → (m * m ≡ a * b)
        → 2 * ((a + b) * (a + b)) ≡ 3 * (c * c)
proof-a a b c m _ a²+b²≡c² 2m≡c m²≡ab =
  begin
    2 * ((a + b) * (a + b))
  ≡⟨ solve (a ∷ b ∷ []) ⟩
    2 * (((a * a) + (b * b)) + (2 * (a * b)))
  ≡⟨ cong (λ x → 2 * (x + (2 * (a * b)))) a²+b²≡c² ⟩
    2 * ((c * c) + (2 * (a * b)))
  ≡⟨ solve (a ∷ b ∷ c ∷ []) ⟩
    (2 * (c * c)) + (4 * (a * b))
  ≡⟨ cong (λ x → (2 * (c * c)) + (4 * x)) (sym m²≡ab) ⟩
    (2 * (c * c)) + (4 * (m * m))
  ≡⟨ solve (c ∷ (m ∷ [])) ⟩
    (2 * (c * c)) + ((2 * m) * (2 * m))
  ≡⟨ cong ((2 * (c * c)) +_) (cong (λ x → x * x) 2m≡c) ⟩
    (2 * (c * c)) + (c * c)
  ≡⟨ solve (c ∷ []) ⟩
    3 * (c * c)
  ∎



proof-b : (a b c m : ℕ)
        → (a ≥ b)
        → (a * a + b * b ≡ c * c)
        → (2 * m ≡ c)
        → (m * m ≡ a * b)
        → 2 * ((a ∸ b) * (a ∸ b)) ≡ c * c
proof-b a b c m a≥b a²+b²≡c² 2m≡c m²≡ab =
  begin
    2 * ((a ∸ b) * (a ∸ b))
  ≡⟨ cong (2 *_) ([a∸b]²≡a²+b²∸2ab a b a≥b) ⟩
    2 * ((a * a) + (b * b) ∸ (2 * (a * b)))
  ≡⟨ cong (λ x → 2 * (x ∸ (2 * (a * b)))) a²+b²≡c² ⟩
    2 * ((c * c) ∸ (2 * (a * b)))
  ≡⟨ *-distribˡ-∸ 2 (c * c) (2 * (a * b)) ⟩
    (2 * (c * c)) ∸ (2 * (2 * (a * b)))
  ≡⟨ cong (λ x → (2 * (c * c)) ∸ (2 * (2 * x))) (sym m²≡ab) ⟩
    (2 * (c * c)) ∸ (2 * (2 * (m * m)))
  ≡⟨ cong (λ x → (2 * (c * c)) ∸ (2 * x)) (sym (*-assoc 2 m m)) ⟩
    (2 * (c * c)) ∸ (2 * ((2 * m) * m))
  ≡⟨ cong (λ x → (2 * (c * c)) ∸ (2 * x)) (*-comm (2 * m) m) ⟩
    (2 * (c * c)) ∸ (2 * (m * (2 * m)))
  ≡⟨ cong (λ x → (2 * (c * c)) ∸ x) (sym (*-assoc 2 m (2 * m))) ⟩
    (2 * (c * c)) ∸ ((2 * m) * (2 * m))
  ≡⟨ cong₂ (λ x y → (2 * (c * c)) ∸ (x * y)) 2m≡c 2m≡c ⟩
    (2 * (c * c)) ∸ (c * c)
  ≡⟨ cong (λ x → x ∸ (c * c)) (cong ((c * c) +_) (+-identityʳ (c * c))) ⟩
    (c * c) + (c * c) ∸ (c * c)
  ≡⟨ m+n∸m≡n (c * c) (c * c) ⟩
    c * c
  ∎



--necessary condition for problem's triangles
--where a b c m not necessarily ∈ ℕ, but don't yet know how to use ℚ or ℝ in Agda
proof-c-lemma : (a b c m : ℕ)
              → (a ≥ b)
              → (a * a + b * b ≡ c * c)
              → (2 * m ≡ c)
              → (m * m ≡ a * b)
              → (a * a) + (b * b) ≡ 4 * (a * b)
proof-c-lemma a b c m _ a²+b²≡c² 2m≡c m²≡ab =
  begin
    (a * a) + (b * b)
  ≡⟨ a²+b²≡c² ⟩
    c * c
  ≡⟨ cong₂ (λ x y → x * y) (sym 2m≡c) (sym 2m≡c) ⟩
    (2 * m) * (2 * m)
  ≡⟨ solve (m ∷ []) ⟩
    4 * (m * m)
  ≡⟨ cong (4 *_) m²≡ab ⟩
    4 * (a * b)
  ∎



eo-⊥ : ∀ (a b : ℕ) → Even a → Odd b → (a * a) + (b * b) ≢ 4 * (a * b)
eo-⊥ a b even-a odd-b a²+b²≡4ab =
     ⊥-elim (even≢odd (*-evenˡ {4} {a * b} (es (os (es (os eo)))))
                      (even+odd≡odd {a * a} {b * b} (*-evenˡ {a} {a} even-a) (*-odd-odd odd-b odd-b))
                      (sym a²+b²≡4ab))

lemma-sa²+sb² : ∀ (a b : ℕ)
                      → (suc a * suc a) + (suc b * suc b) ≡ 4 * (suc a * suc b)
                      → (2 * (1 + a + b)) + ((a * a) + (b * b)) ≡ 2 * (2 * (suc a * suc b))
lemma-sa²+sb² a b sa²+sb²≡4*sa*sb =
  begin
    (2 * (1 + a + b)) + ((a * a) + (b * b))
  ≡⟨ subst (_≡_ (2 * (1 + a + b) + ((a * a) + (b * b)))) sa²+sb²≡4*sa*sb (solve (a ∷ (b ∷ []))) ⟩
    4 * (suc a * suc b)
  ≡⟨ solve (a ∷ (b ∷ [])) ⟩
    2 * (2 * (suc a * suc b))
  ∎

lemma-a²+b²-exp : ∀ (a b ka kb : ℕ)
                → (a * a) ≡ 4 * (ka * ka)
                → (b * b) ≡ 4 * (kb * kb)
                → (a * a) + (b * b) ≡ 4 * (ka * ka + kb * kb)
lemma-a²+b²-exp a b ka kb a²≡4ka² b²=4kb² =
  begin
    a * a + b * b
  ≡⟨ cong₂ (λ x y → x + y) a²≡4ka² b²=4kb² ⟩
    (4 * (ka * ka)) + (4 * (kb * kb))
  ≡⟨ solve (ka ∷ (kb ∷ [])) ⟩
    4 * (ka * ka + kb * kb)
  ∎

lemma-a²+b² : ∀ (a b : ℕ)
            → Even a → Even b
            → ∃[ ka ](∃[ kb ]((a ≡ 2 * ka) × (b ≡ 2 * kb) × ((a * a) + (b * b) ≡ 4 * ((ka * ka) + (kb * kb)))))
lemma-a²+b² a b even-a even-b with even-a→a²≡4k² a even-a | even-a→a²≡4k² b even-b
... | ka , a≡2ka , a²≡4ka² | kb , b≡2kb , b²≡4kb² = ka , kb , a≡2ka , (b≡2kb , lemma-a²+b²-exp a b ka kb a²≡4ka² b²≡4kb²)

lemma-rearrange : ∀ (a b : ℕ)
                → Even a → Even b
                → (2 * (1 + a + b)) + ((a * a) + (b * b)) ≡ 2 * (2 * (suc a * suc b))
                → ∃[ ka ](∃[ kb ]((2 * ((1 + a + b) + (2 * (ka * ka + kb * kb)))) ≡ 2 * (2 * (suc a * suc b))))
lemma-rearrange a b even-a even-b p with lemma-a²+b² a b even-a even-b
... | ka , kb , a≡2ka , b≡2kb , a²+b²≡4[ka²+kb²] = ka , (kb , (
  begin
    2 * ((1 + a + b) + (2 * (ka * ka + kb * kb)))
  ≡⟨ *-distribˡ-+ 2 (1 + a + b) (2 * (ka * ka + kb * kb)) ⟩
    2 * (1 + a + b) + 2 * (2 * (ka * ka + kb * kb))
  ≡⟨ cong (λ x → 2 * (1 + a + b) + x) (sym (*-assoc 2 2 (ka * ka + kb * kb))) ⟩
    2 * (1 + a + b) + (4 * (ka * ka + kb * kb))
  ≡⟨ cong (λ x → 2 * (1 + a + b) + x) (sym a²+b²≡4[ka²+kb²]) ⟩
    2 * (1 + a + b) + ((a * a) + (b * b))
  ≡⟨ p ⟩
    2 * (2 * (suc a * suc b))
  ∎))

oo-⊥ : ∀ (a b : ℕ) → Odd a → Odd b → (a * a) + (b * b) ≢ 4 * (a * b)
oo-⊥ (suc a) (suc b) (os even-a) (os even-b) sa²+sb²≡4*sa*sb =
  let
    p = lemma-sa²+sb² a b sa²+sb²≡4*sa*sb
    ka , kb , q = lemma-rearrange a b even-a even-b p
    r = *-cancelˡ-≡ ((1 + a + b) + (2 * (ka * ka + kb * kb))) (2 * (suc a * suc b)) 2 q
    elhs = *-evenˡ {2} {suc a * suc b} (es (os eo))
    erhs = odd+even≡odd (odd+even≡odd {1} {a + b} (os eo) (even+even≡even even-a even-b))
                        (*-evenˡ {2} {ka * ka + kb * kb} (es (os eo)))
  in
    ⊥-elim (even≢odd elhs erhs (sym r))

a²+b²≡4ab→even-a-and-even-b : ∀ (a b : ℕ) → (a * a) + (b * b) ≡ 4 * (a * b) → Even a × Even b
a²+b²≡4ab→even-a-and-even-b a b a²+b²≡4ab with even-or-odd a | even-or-odd b
... | inj₁ ea | inj₁ eb = ea , eb
... | inj₁ ea | inj₂ ob = ⊥-elim (eo-⊥ a b ea ob a²+b²≡4ab)
... | inj₂ oa | inj₁ eb = ⊥-elim (eo-⊥ b a eb oa (subst₂ _≡_ (+-comm (a * a) (b * b)) (cong (4 *_) (*-comm a b)) a²+b²≡4ab))
... | inj₂ oa | inj₂ ob = ⊥-elim (oo-⊥ a b oa ob a²+b²≡4ab)



a*a≡0→a≡0 : ∀ (a : ℕ) → a * a ≡ 0 → a ≡ 0
a*a≡0→a≡0 zero _ = refl

sa≢0 : ∀ (a : ℕ) → suc a ≢ 0
sa≢0 zero ()
sa≢0 (suc a) ()

sa/2<sa : ∀ (a k : ℕ) → suc a ≡ 2 * k → k < suc a
sa/2<sa a (suc k) refl rewrite +-identityʳ k | +-comm k (suc k) = s≤s (s≤s (a≤b→a≤b+c k k k (a≤a k)))

unique-solution : ∀ (a b : ℕ) → Acc _<_ a → (a * a) + (b * b) ≡ 4 * (a * b) → (a ≡ zero) × (b ≡ zero)
unique-solution zero b _ b²≡0 = refl , a*a≡0→a≡0 b b²≡0
unique-solution (suc a) b (acc rs) sa²+b²≡4*sa*b =
  let
    even-sa , even-b = a²+b²≡4ab→even-a-and-even-b (suc a) b sa²+b²≡4*sa*b
    
    sa/2 , b/2 , sa≡2*sa/2 , b≡2*b/2 , sa²+b²≡4[[sa/2]²+[b/2]²] = lemma-a²+b² (suc a) b even-sa even-b
    
    new-eq-lemma : 4 * ((sa/2 * sa/2) + (b/2 * b/2)) ≡ 4 * (4 * (sa/2 * b/2))
    new-eq-lemma =
      begin
        4 * (sa/2 * sa/2 + b/2 * b/2)
      ≡⟨ sym sa²+b²≡4[[sa/2]²+[b/2]²] ⟩
        (suc a * suc a + b * b)
      ≡⟨ sa²+b²≡4*sa*b ⟩
        4 * (suc a * b)
      ≡⟨ cong (4 *_) (cong₂ (λ x y → x * y) sa≡2*sa/2 b≡2*b/2) ⟩
        4 * ((2 * sa/2) * (2 * b/2))
      ≡⟨ cong (4 *_) (*-swap 2 sa/2 (2 * b/2)) ⟩
        4 * (2 * (2 * b/2) * sa/2)
      ≡⟨ cong (λ x → 4 * (x * sa/2)) (sym (*-assoc 2 2 b/2)) ⟩
        4 * ((4 * b/2) * sa/2)
      ≡⟨ cong (λ x → 4 * x) (*-assoc 4 b/2 sa/2) ⟩
        4 * (4 * (b/2 * sa/2))
      ≡⟨ cong (λ x → 4 * (4 * x)) (*-comm b/2 sa/2) ⟩
        4 * (4 * (sa/2 * b/2))
      ∎

    new-eq : (sa/2 * sa/2) + (b/2 * b/2) ≡ 4 * (sa/2 * b/2)
    new-eq = *-cancelˡ-≡ (sa/2 * sa/2 + b/2 * b/2) (4 * (sa/2 * b/2)) 4 new-eq-lemma

    sa/2≡0 , b/2≡0 = unique-solution sa/2 b/2 (rs (sa/2<sa a sa/2 sa≡2*sa/2)) new-eq

    sa≡0 : suc a ≡ 0
    sa≡0 =
      begin
        suc a
      ≡⟨ sa≡2*sa/2 ⟩
        2 * sa/2
      ≡⟨ cong (2 *_) sa/2≡0 ⟩
        2 * 0
      ≡⟨ refl ⟩
        0
      ∎
  in
    ⊥-elim (sa≢0 a sa≡0)



a>0→a≢0 : ∀ (a : ℕ) → a > 0 → a ≢ 0
a>0→a≢0 zero () a≡0
a>0→a≢0 (suc a) (s≤s a>0) ()

proof-c : (a b c m : ℕ)
        → (a ≥ b)
        → (a * a + b * b ≡ c * c)
        → (2 * m ≡ c)
        → (m * m ≡ a * b)
        → (a > 0) → (b > 0) → (c > 0)
        → ⊥
proof-c a b c m a≥b a²+b²≡c² 2m≡c m²≡ab a>0 b>0 c>0 = ⊥-elim (a>0→a≢0 a a>0 (proj₁ (unique-solution a b (<-wellFounded a) (proof-c-lemma a b c m a≥b a²+b²≡c² 2m≡c m²≡ab))))
