module Polynomials.Binomials where



open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_; z≤n; s≤s; _≥_; _∸_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-assoc; *-identityˡ; *-identityʳ)
open import Data.Nat.Properties using (m+n∸m≡n; ∸-+-assoc; +-∸-comm; *-distribˡ-∸)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (_²; _³; a²≡a*a; a≤a; a≤b→a≤b+c)



[a+b]²≡a²+2ab+b² : ∀ (a b : ℕ) → (a + b) ² ≡ (a ²) + (2 * (a * b)) + (b ²)
[a+b]²≡a²+2ab+b² a b =
  begin
    (a + b) ²
  ≡⟨⟩
    (a + b) * ((a + b) * 1)
  ≡⟨ cong (λ x → (a + b) * x) (*-identityʳ (a + b)) ⟩
    (a + b) * (a + b)
  ≡⟨ *-distribʳ-+ (a + b) a b ⟩
    (a * (a + b)) + (b * (a + b))
  ≡⟨ cong (_+ (b * (a + b))) (*-distribˡ-+ a a b) ⟩
    ((a * a) + (a * b)) + (b * (a + b))
  ≡⟨ cong (((a * a) + (a * b)) +_) (*-distribˡ-+ b a b) ⟩
    ((a * a) + (a * b)) + ((b * a) + (b * b))
  ≡⟨ cong (((a * a) + (a * b)) +_) (cong (_+ (b * b)) (*-comm b a)) ⟩
    ((a * a) + (a * b)) + ((a * b) + (b * b))
  ≡⟨ sym (+-assoc ((a * a) + (a * b)) (a * b) (b * b)) ⟩
    ((a * a) + (a * b) + (a * b)) + (b * b)
  ≡⟨ cong (_+ (b * b)) (+-assoc (a * a) (a * b) (a * b)) ⟩
    (a * a) + ((a * b) + (a * b)) + (b * b)
  ≡⟨ cong (_+ (b * b)) (cong ((a * a) +_) (cong ((a * b) +_) (sym (+-identityʳ (a * b))))) ⟩
    (a * a) + (2 * (a * b)) + (b * b)
  ≡⟨ cong₂ (λ x y → x + (2 * (a * b)) + y) (sym (a²≡a*a a)) (sym (a²≡a*a b)) ⟩
    (a ²) + (2 * (a * b)) + (b ²)
  ∎



[1+n]²≡1+2n+n² : ∀ (n : ℕ) → (1 + n) ² ≡ 1 + (2 * n) + (n ²)
[1+n]²≡1+2n+n² n rewrite +-identityʳ n
                       | *-identityʳ n
                       | *-comm n (suc n)
                       | sym (+-assoc n n (n * n))
                       = refl



sa*sb≡1+a+b+ab : ∀ (a b : ℕ) → suc a * suc b ≡ 1 + a + b + (a * b)
sa*sb≡1+a+b+ab a b rewrite *-comm a (suc b)
                         | sym (+-assoc b a (b * a))
                         | +-comm b a
                         | *-comm b a
                         = refl

a[b+c+d+e]≡ab+ac+ad+ae : ∀ (a b c d e : ℕ) → a * (b + c + d + e) ≡ (a * b) + (a * c) + (a * d) + (a * e)
a[b+c+d+e]≡ab+ac+ad+ae a b c d e rewrite *-distribˡ-+ a (b + c + d) e
                                       | *-distribˡ-+ a (b + c) d
                                       | *-distribˡ-+ a b c
                                       = refl

lemma-2a≤2a+a² : ∀ (a : ℕ) → (2 * a) ≤ (a + a + (a * a))
lemma-2a≤2a+a² a rewrite +-identityʳ a = a≤b→a≤b+c (a + a) (a + a) (a * a) (a≤a (a + a))

lemma-2a+a²-2a≡a² : ∀ a → (a + a + (a * a)) ∸ (2 * a) ≡ a * a
lemma-2a+a²-2a≡a² a =
  begin
    (a + a + (a * a)) ∸ (2 * a)
  ≡⟨ cong (λ x → (x + (a * a)) ∸ (2 * a)) (cong (a +_) (sym (+-identityʳ a))) ⟩
    ((2 * a) + (a * a)) ∸ (2 * a)
  ≡⟨ m+n∸m≡n (2 * a) (a * a) ⟩
    a * a
  ∎

[a∸b]²≡a²+b²∸2ab : ∀ (a b : ℕ) → a ≥ b → (a ∸ b) * (a ∸ b) ≡ (a * a) + (b * b) ∸ (2 * (a * b))
[a∸b]²≡a²+b²∸2ab a zero _ rewrite *-comm a 0 | +-identityʳ (a * a) = refl
[a∸b]²≡a²+b²∸2ab (suc a) (suc b) (s≤s a≥b) =
  begin
    (suc a ∸ suc b) * (suc a ∸ suc b)
  ≡⟨ refl ⟩
    (a ∸ b) * (a ∸ b)
  ≡⟨ [a∸b]²≡a²+b²∸2ab a b a≥b ⟩
    (a * a) + (b * b) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → x ∸ (2 * (a * b))) (+-comm (a * a) (b * b)) ⟩
    (b * b) + (a * a) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (x + (a * a)) ∸ (2 * (a * b))) (sym (lemma-2a+a²-2a≡a² b)) ⟩
    (((b + b + (b * b)) ∸ (2 * b)) + (a * a)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → x ∸ (2 * (a * b))) (sym (+-∸-comm (a * a) (lemma-2a≤2a+a² b))) ⟩
    (((b + b + (b * b)) + (a * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (x ∸ (2 * b)) ∸ (2 * (a * b))) (+-comm (b + b + (b * b)) (a * a)) ⟩
    (((a * a) + (b + b + (b * b))) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → ((x + (b + b + (b * b))) ∸ (2 * b)) ∸ (2 * (a * b))) (sym (lemma-2a+a²-2a≡a² a)) ⟩
    ((((a + a + (a * a)) ∸ (2 * a)) + (b + b + (b * b))) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (x ∸ (2 * b)) ∸ (2 * (a * b))) (sym (+-∸-comm (b + b + (b * b)) (lemma-2a≤2a+a² a))) ⟩
    ((((a + a + (a * a)) + (b + b + (b * b))) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ refl ⟩
    (((((1 + a + a + (a * a)) ∸ 1) + ((1 + b + b + (b * b)) ∸ 1)) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong₂ (λ x y → ((((x ∸ 1) + (y ∸ 1)) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b)))
           (sym (sa*sb≡1+a+b+ab a a))
           (sym (sa*sb≡1+a+b+ab b b)) ⟩
    (((((suc a * suc a) ∸ 1) + ((suc b * suc b) ∸ 1)) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → ((x ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))) (+-comm ((suc a * suc a) ∸ 1) ((suc b * suc b) ∸ 1)) ⟩
    (((((suc b * suc b) ∸ 1) + ((suc a * suc a) ∸ 1)) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ refl ⟩
    (((((suc b * suc b) + ((suc a * suc a) ∸ 1)) ∸ 1) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (((x ∸ 1) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))) (+-comm (suc b * suc b) ((suc a * suc a) ∸ 1)) ⟩
    ((((((suc a * suc a) ∸ 1) + (suc b * suc b)) ∸ 1) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (((x ∸ 1) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))) (+-∸-comm {suc a * suc a} (suc b * suc b) {1} (s≤s z≤n)) ⟩
    ((((((suc a * suc a) + (suc b * suc b)) ∸ 1) ∸ 1) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (((x ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b)))) (∸-+-assoc ((suc a * suc a) + (suc b * suc b)) 1 1) ⟩
    (((((suc a * suc a) + (suc b * suc b)) ∸ (1 + 1)) ∸ (2 * a)) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → (x ∸ (2 * b)) ∸ (2 * (a * b))) (∸-+-assoc ((suc a * suc a) + (suc b * suc b)) 2 (2 * a)) ⟩
    ((((suc a * suc a) + (suc b * suc b)) ∸ (2 + (2 * a))) ∸ (2 * b)) ∸ (2 * (a * b))
  ≡⟨ cong (λ x → x ∸ (2 * (a * b))) (∸-+-assoc ((suc a * suc a) + (suc b * suc b)) (2 + (2 * a)) (2 * b)) ⟩
    (((suc a * suc a) + (suc b * suc b)) ∸ (2 + (2 * a) + (2 * b))) ∸ (2 * (a * b))
  ≡⟨ ∸-+-assoc ((suc a * suc a) + (suc b * suc b)) (2 + (2 * a) + (2 * b)) (2 * (a * b)) ⟩
    ((suc a * suc a) + (suc b * suc b)) ∸ ((2 + (2 * a) + (2 * b)) + (2 * (a * b)))
  ≡⟨ cong (λ x → (suc a * suc a) + (suc b * suc b) ∸ x) (sym (a[b+c+d+e]≡ab+ac+ad+ae 2 1 a b (a * b))) ⟩
    (suc a * suc a) + (suc b * suc b) ∸ (2 * (1 + a + b + (a * b)))
  ≡⟨ cong (λ x → (suc a * suc a) + (suc b * suc b) ∸ (2 * x)) (sym (sa*sb≡1+a+b+ab a b)) ⟩
    (suc a * suc a) + (suc b * suc b) ∸ (2 * (suc a * suc b))
  ∎



[a+b]∸[b+c]≡a∸c : ∀ (a b c : ℕ) → (a + b) ∸ (b + c) ≡ a ∸ c
[a+b]∸[b+c]≡a∸c a zero c rewrite +-identityʳ a = refl
[a+b]∸[b+c]≡a∸c a (suc b) c rewrite +-comm a (suc b)
                                  | +-comm b a
                                  = [a+b]∸[b+c]≡a∸c a b c

[a+b][a∸b]≡a²∸b² : ∀ (a b : ℕ) → a ≥ b → (a + b) * (a ∸ b) ≡ (a * a) ∸ (b * b)
[a+b][a∸b]≡a²∸b² a zero _ rewrite +-identityʳ a = refl
[a+b][a∸b]≡a²∸b² (suc a) (suc b) (s≤s a≥b) =
  begin
    (suc a + suc b) * (suc a ∸ suc b)
  ≡⟨ *-distribˡ-∸ (suc a + suc b) (suc a) (suc b) ⟩
    ((suc a + suc b) * suc a) ∸ ((suc a + suc b) * suc b)
  ≡⟨ cong₂ (λ x y → x ∸ y) (*-distribʳ-+ (suc a) (suc a) (suc b)) (*-distribʳ-+ (suc b) (suc a) (suc b)) ⟩
    ((suc a * suc a) + (suc b * suc a)) ∸ ((suc a * suc b) + (suc b * suc b))
  ≡⟨ cong (λ x → ((suc a * suc a) + x) ∸ ((suc a * suc b) + (suc b * suc b))) (*-comm (suc b) (suc a)) ⟩
    ((suc a * suc a) + (suc a * suc b)) ∸ ((suc a * suc b) + (suc b * suc b))
  ≡⟨ [a+b]∸[b+c]≡a∸c (suc a * suc a) (suc a * suc b) (suc b * suc b) ⟩
    (suc a * suc a) ∸ (suc b * suc b)
  ∎



a[a+b]²≡a³+2a²b+ab² : ∀ (a b : ℕ) → a * (a + b) ² ≡ a ³ + (2 * ((a ²) * b)) + (a * (b ²))
a[a+b]²≡a³+2a²b+ab² a b =
  begin
    a * (a + b) ²
  ≡⟨ cong (a *_) ([a+b]²≡a²+2ab+b² a b) ⟩
    a * (a ² + 2 * (a * b) + b ²)
  ≡⟨ *-distribˡ-+ a ((a ²) + 2 * (a * b)) (b ²) ⟩
    a * (a ² + 2 * (a * b)) + (a * b ²)
  ≡⟨ cong (_+ (a * b ²)) (*-distribˡ-+ a (a ²) (2 * (a * b))) ⟩
    (a * (a ²) + (a * (2 * (a * b)))) + (a * b ²)
  ≡⟨ cong (_+ (a * b ²)) (cong (a ³ +_) (sym (*-assoc a 2 (a * b)))) ⟩
    (a ³) + ((a * 2) * (a * b)) + (a * b ²)
  ≡⟨ cong (_+ (a * b ²)) (cong (a ³ +_) (cong (_* (a * b)) (*-comm a 2))) ⟩
    (a ³) + ((2 * a) * (a * b)) + (a * b ²)
  ≡⟨ cong (_+ (a * b ²)) (cong (a ³ +_) (*-assoc 2 a (a * b))) ⟩
    (a ³) + (2 * (a * (a * b))) + (a * b ²)
  ≡⟨ cong (λ x → (a ³) + (2 * x) + (a * b ²)) (sym (*-assoc a a b)) ⟩
    (a ³) + (2 * ((a * a) * b)) + (a * b ²)
  ≡⟨ cong (λ x → (a ³) + (2 * (x * b)) + (a * b ²)) (sym (a²≡a*a a)) ⟩
    (a ³) + (2 * ((a ²) * b)) + (a * (b ²))
  ∎



lemma-[[a+b]+c]+[[d+e]+f] : ∀ a b c d e f → ((a + b) + c) + ((d + e) + f) ≡ a + (b + f) + (c + e) + d
lemma-[[a+b]+c]+[[d+e]+f] a b c d e f rewrite +-comm (d + e) f
                                            | sym (+-assoc (a + b + c) f (d + e))
                                            | +-assoc (a + b) c f
                                            | +-comm c f
                                            | sym (+-assoc (a + b) f c)
                                            | +-assoc a b f
                                            | +-comm d e
                                            | +-assoc (a + (b + f)) c (e + d)
                                            | sym (+-assoc c e d)
                                            | sym (+-assoc (a + (b + f)) (c + e) d)
                                            = refl



[a+b]³=a³+3a²b+3ab²+b³ : ∀ (a b : ℕ) → (a + b) ³ ≡ (a ³) + (3 * ((a ²) * b)) + (3 * (a * (b ²))) + (b ³)
[a+b]³=a³+3a²b+3ab²+b³ a b =
  begin
    (a + b) ³
  ≡⟨⟩
    (a + b) * (a + b) ²
  ≡⟨ *-distribʳ-+ ((a + b) ²) a b ⟩
    (a * ((a + b) ²)) + (b * ((a + b) ²))
  ≡⟨ cong (_+ b * ((a + b) ²)) (a[a+b]²≡a³+2a²b+ab² a b) ⟩
    (a ³ + (2 * ((a ²) * b)) + (a * (b ²))) + (b * ((a + b) ²))
  ≡⟨ cong (a ³ + (2 * ((a ²) * b)) + (a * (b ²)) +_) (cong (b *_) (cong _² (+-comm a b))) ⟩
    (a ³ + (2 * ((a ²) * b)) + (a * (b ²))) + (b * ((b + a) ²))
  ≡⟨ cong (a ³ + (2 * ((a ²) * b)) + (a * (b ²)) +_) (a[a+b]²≡a³+2a²b+ab² b a) ⟩
    ((a ³ + (2 * ((a ²) * b))) + (a * (b ²))) + ((b ³ + (2 * ((b ²) * a))) + (b * (a ²)))
  ≡⟨ lemma-[[a+b]+c]+[[d+e]+f] (a ³) (2 * ((a ²) * b)) (a * (b ²)) (b ³) (2 * ((b ²) * a)) (b * (a ²)) ⟩
    (a ³) + ((2 * ((a ²) * b)) + (b * (a ²))) + ((a * (b ²)) + (2 * ((b ²) * a))) + (b ³)
  ≡⟨ cong (λ x → (a ³) + ((2 * ((a ²) * b)) + x) + ((a * (b ²)) + (2 * ((b ²) * a))) + (b ³)) (*-comm b (a ²)) ⟩
    (a ³) + ((2 * ((a ²) * b)) + ((a ²) * b)) + ((a * (b ²)) + (2 * ((b ²) * a))) + (b ³)
  ≡⟨ cong (λ x → (a ³) + x + ((a * (b ²)) + (2 * ((b ²) * a))) + (b ³)) (+-comm (2 * ((a ²) * b)) ((a ²) * b)) ⟩
    (a ³) + (3 * ((a ²) * b)) + ((a * (b ²)) + (2 * ((b ²) * a))) + (b ³)
  ≡⟨ cong (λ x → (a ³) + (3 * ((a ²) * b)) + ((a * (b ²)) + (2 * x)) + (b ³)) (*-comm (b ²) a) ⟩
    (a ³) + (3 * ((a ²) * b)) + (3 * (a * (b ²))) + (b ³)
  ∎



[1+n]³=1+3n+3n²+n³ : ∀ (n : ℕ) → (1 + n) ³ ≡ 1 + (3 * n) + (3 * n ²) + n ³
[1+n]³=1+3n+3n²+n³ n =
  begin
    (1 + n) ³
  ≡⟨ [a+b]³=a³+3a²b+3ab²+b³ 1 n ⟩
    1 + (3 * (1 * n)) + (3 * (1 * (n ²))) + (n ³)
  ≡⟨ cong (λ x → 1 + (3 * x) + (3 * (1 * (n ²))) + (n ³)) (*-identityˡ n) ⟩
    1 + (3 * n) + (3 * (1 * (n ²))) + (n ³)
  ≡⟨ cong (λ x → 1 + (3 * n) + (3 * x) + (n ³)) (*-identityˡ (n ²)) ⟩
    1 + (3 * n) + (3 * (n ²)) + (n ³)
  ∎
