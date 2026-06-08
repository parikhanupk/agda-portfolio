module Polynomials.Binomials where



open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Utilities using (_²; _³; a²≡a*a)



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
