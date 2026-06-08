module Series.Properties.Nicomachus where



open import Data.Nat using (ℕ; zero; suc; _>_; _+_; z≤n; s≤s; _*_)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-identityˡ; *-comm; +-assoc; *-assoc; *-distribˡ-+; *-distribʳ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Polynomials.Binomials using ([a+b]²≡a²+2ab+b²)



downFrom : (n : ℕ) → (n > 0) → List ℕ
downFrom (suc zero) (s≤s z≤n) = 1 ∷ []
downFrom (suc (suc n)) (s≤s z≤n) = suc (suc n) ∷ downFrom (suc n) (s≤s z≤n)

_ : downFrom 3 (s≤s z≤n) ≡ (3 ∷ 2 ∷ 1 ∷ [])
_ = refl



sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + (sum xs)

_ : sum (downFrom 3 (s≤s z≤n)) ≡ 6
_ = refl



map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs



_² : ℕ → ℕ
n ² = n * n

_³ : ℕ → ℕ
n ³ = n * n * n



[a+b]²≡a²+b²+2ab : ∀ (a b : ℕ) → (a + b) ² ≡ a ² + b ² + (2 * (a * b))
[a+b]²≡a²+b²+2ab a b rewrite [a+b]²≡a²+2ab+b² a b
                           | +-assoc (a ²) (2 * (a * b)) (b ²)
                           | +-comm (2 * (a * b)) (b ²)
                           | sym (+-assoc (a ²) (b ²) (2 * (a * b)))
                           = refl



a+b+c≡a+c+b : ∀ (a b c : ℕ) → a + b + c ≡ a + c + b
a+b+c≡a+c+b a b c rewrite +-assoc a b c
                        | +-comm b c
                        | +-assoc a c b
                        = refl



n+n+n≡3*n : ∀ (n : ℕ) → n + n + n ≡ 3 * n
n+n+n≡3*n zero = refl
n+n+n≡3*n (suc n) rewrite +-identityʳ n
                        | +-assoc n (suc n) (suc n)
                        = refl



n+n≡n*2 : ∀ (n : ℕ) → n + n ≡ n * 2
n+n≡n*2 n rewrite *-comm n 2
                | +-identityʳ n
                = sym refl



2*Σ[n+1]≡[n+1]*[n+2] : ∀ (n : ℕ) → 2 * sum (downFrom (1 + n) (s≤s z≤n)) ≡ (1 + n) * (2 + n)
2*Σ[n+1]≡[n+1]*[n+2] zero = refl
2*Σ[n+1]≡[n+1]*[n+2] (suc n) =
  begin
    2 * sum (downFrom (2 + n) (s≤s z≤n))
  ≡⟨⟩
    2 * ((2 + n) + sum (downFrom (1 + n) (s≤s z≤n)))
  ≡⟨ *-distribˡ-+ 2 (2 + n) (sum (downFrom (1 + n) (s≤s z≤n))) ⟩
    (2 * (2 + n)) + (2 * sum (downFrom (1 + n) (s≤s z≤n)))
  ≡⟨ cong ((2 * (2 + n)) +_) (2*Σ[n+1]≡[n+1]*[n+2] n) ⟩
    (2 * (2 + n)) + ((1 + n) * (2 + n))
  ≡⟨ cong (_+ ((1 + n) * (2 + n))) (*-comm 2 (2 + n)) ⟩
    ((2 + n) * 2) + ((1 + n) * (2 + n))
  ≡⟨ cong (_+ ((1 + n) * (2 + n))) (sym (n+n≡n*2 (2 + n))) ⟩
    (2 + n) + (2 + n) + ((1 + n) * (2 + n))
  ≡⟨ cong ((2 + n) + (2 + n) +_) (*-distribʳ-+ (2 + n) 1 n) ⟩
    (2 + n) + (2 + n) + ((1 * (2 + n)) + (n * (2 + n)))
  ≡⟨ cong ((2 + n) + (2 + n) +_) (cong (_+ n * (2 + n)) (*-identityˡ (2 + n))) ⟩
    ((2 + n) + (2 + n)) + ((2 + n) + (n * (2 + n)))
  ≡⟨ sym (+-assoc ((2 + n) + (2 + n)) (2 + n) (n * (2 + n))) ⟩
    (((2 + n) + (2 + n)) + (2 + n)) + (n * (2 + n))
  ≡⟨ cong (_+ (n * (2 + n))) (n+n+n≡3*n (2 + n)) ⟩
    (3 * (2 + n)) + (n * (2 + n))
  ≡⟨ sym (*-distribʳ-+ (2 + n) 3 n) ⟩
    (3 + n) * (2 + n)
  ≡⟨ *-comm (3 + n) (2 + n) ⟩
    (2 + n) * (3 + n)
  ∎



2*[[n+2]*Σ[n+1]]≡[n+2]²+[[n+2]²*n] : ∀ (n : ℕ) → 2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n)))) ≡ (2 + n) ² + ((2 + n) ² * n)
2*[[n+2]*Σ[n+1]]≡[n+2]²+[[n+2]²*n] n =
  begin
    2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n))))
  ≡⟨ sym (*-assoc 2 (2 + n) (sum (downFrom (1 + n) (s≤s z≤n)))) ⟩
    (2 * (2 + n)) * (sum (downFrom (1 + n) (s≤s z≤n)))
  ≡⟨ cong (_* sum (downFrom (1 + n) (s≤s z≤n))) (*-comm 2 (2 + n)) ⟩
    ((2 + n) * 2) * (sum (downFrom (1 + n) (s≤s z≤n)))
  ≡⟨ *-assoc (2 + n) 2 (sum (downFrom (1 + n) (s≤s z≤n))) ⟩
    (2 + n) * (2 * (sum (downFrom (1 + n) (s≤s z≤n))))
  ≡⟨ cong ((2 + n) *_) (2*Σ[n+1]≡[n+1]*[n+2] n) ⟩
    (2 + n) * ((1 + n) * (2 + n))
  ≡⟨ cong ((2 + n) *_) (*-distribʳ-+ (2 + n) 1 n) ⟩
    (2 + n) * ((1 * (2 + n)) + (n * (2 + n)))
  ≡⟨ cong ((2 + n) *_) (cong (_+ (n * (2 + n))) (*-identityˡ (2 + n))) ⟩
    (2 + n) * ((2 + n) + (n * (2 + n)))
  ≡⟨ *-distribˡ-+ (2 + n) (2 + n) (n * (2 + n)) ⟩
    ((2 + n) * (2 + n)) + ((2 + n) * (n * (2 + n)))
  ≡⟨⟩
    (2 + n) ² + ((2 + n) * (n * (2 + n)))
  ≡⟨ cong ((2 + n) ² +_) (cong ((2 + n) *_) (*-comm n (2 + n))) ⟩
    (2 + n) ² + ((2 + n) * ((2 + n) * n))
  ≡⟨ cong ((2 + n) ² +_) (sym (*-assoc (2 + n) (2 + n) n)) ⟩
    (2 + n) ² + ((2 + n) * (2 + n) * n)
  ≡⟨⟩
    (2 + n) ² + ((2 + n) ² * n)
  ∎



[n+2]²+[[n+2]²*n]≡2*[[n+2]*Σ[n+1]] : ∀ (n : ℕ) → (2 + n) ² + ((2 + n) ² * n) ≡ 2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n))))
[n+2]²+[[n+2]²*n]≡2*[[n+2]*Σ[n+1]] n = sym (2*[[n+2]*Σ[n+1]]≡[n+2]²+[[n+2]²*n] n)



[n+2]³+[Σ[n+1]]²≡[Σ[n+2]]² : ∀ (n : ℕ) → (suc (suc n)) ³ + (sum (downFrom (suc n) (s≤s z≤n))) ² ≡ (sum (downFrom (suc (suc n)) (s≤s z≤n))) ²
[n+2]³+[Σ[n+1]]²≡[Σ[n+2]]² n =
  begin
    (suc (suc n)) ³ + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨⟩
    (2 + n) ² * (2 + n) + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨ cong (_+ (sum (downFrom (suc n) (s≤s z≤n))) ²) (*-distribˡ-+ ((2 + n) ²) 2 n) ⟩
    ((2 + n) ² * 2) + ((2 + n) ² * n) + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨ cong (_+ (sum (downFrom (suc n) (s≤s z≤n))) ²) (cong (_+ ((2 + n) ² * n)) (sym (n+n≡n*2 ((2 + n) ²)))) ⟩
    (((2 + n) ² + (2 + n) ²) + ((2 + n) ² * n)) + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨ cong (_+ (sum (downFrom (suc n) (s≤s z≤n))) ²) (+-assoc ((2 + n) ²) ((2 + n) ²) ((2 + n) ² * n)) ⟩
    (2 + n) ² + ((2 + n) ² + ((2 + n) ² * n)) + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨ cong (_+ (sum (downFrom (suc n) (s≤s z≤n))) ²) (cong ((2 + n) ² +_) ([n+2]²+[[n+2]²*n]≡2*[[n+2]*Σ[n+1]] n)) ⟩
    (2 + n) ² + (2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n))))) + (sum (downFrom (1 + n) (s≤s z≤n))) ²
  ≡⟨ a+b+c≡a+c+b ((2 + n) ²) (2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n))))) ((sum (downFrom (1 + n) (s≤s z≤n))) ²) ⟩
    (2 + n) ² + (sum (downFrom (1 + n) (s≤s z≤n))) ² + (2 * ((2 + n) * (sum (downFrom (1 + n) (s≤s z≤n)))))
  ≡⟨ sym ([a+b]²≡a²+b²+2ab (2 + n) (sum (downFrom (1 + n) (s≤s z≤n)))) ⟩
    (sum (downFrom (suc (suc n)) (s≤s z≤n))) ²
  ∎



sum-of-cubes≡square-of-sum : ∀ (n : ℕ) → (n>0 : n > 0) → sum (map _³ (downFrom n n>0)) ≡ (sum (downFrom n n>0)) ²
sum-of-cubes≡square-of-sum (suc zero) (s≤s z≤n) = refl
sum-of-cubes≡square-of-sum (suc (suc n)) (s≤s z≤n) =
  begin
    sum (map _³ (downFrom (suc (suc n)) (s≤s z≤n)))
  ≡⟨⟩
    sum ((suc (suc n)) ³ ∷ map _³ (downFrom (suc n) (s≤s z≤n)))
  ≡⟨⟩
    (suc (suc n)) ³ + sum (map _³ (downFrom (suc n) (s≤s z≤n)))
  ≡⟨ cong (_³ (suc (suc n)) +_) (sum-of-cubes≡square-of-sum (suc n) (s≤s z≤n)) ⟩
    (suc (suc n)) ³ + (sum (downFrom (suc n) (s≤s z≤n))) ²
  ≡⟨ [n+2]³+[Σ[n+1]]²≡[Σ[n+2]]² n ⟩
    (sum (downFrom (suc (suc n)) (s≤s z≤n))) ²
  ∎
