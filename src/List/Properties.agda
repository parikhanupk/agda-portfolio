module List.Properties where



open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; length; _++_; map; take; drop)
open import Data.Bool.ListAction using (any)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; _≢_)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (Bool; false; true)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to zeroᶠ; suc to sucᶠ)
open import Data.Vec using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)



--problem 1
length-dist : ∀ {A : Set} (xs ys : List A)
            → length (xs ++ ys) ≡ length xs + length ys
length-dist [] ys = refl
length-dist (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    1 + length (xs ++ ys)
  ≡⟨ cong (1 +_) (length-dist xs ys) ⟩
    1 + (length xs + length ys)
  ≡⟨ refl ⟩
    length (x ∷ xs) + length ys
  ∎



--problem 2
map-++-dist : ∀ {A B : Set} (f : A → B) (xs ys : List A)
            → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-dist f [] ys = refl
map-++-dist f (x ∷ xs) ys = cong (f x ∷_) (map-++-dist f xs ys)



--problem 3
++-identityʳ : ∀ {A : Set} (xs : List A)
             → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)



reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ (x ∷ [])



++-assoc : ∀ {A : Set} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨ refl ⟩
    (x ∷ (xs ++ ys)) ++ zs
  ≡⟨ refl ⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨ refl ⟩
    (x ∷ xs) ++ ys ++ zs
  ∎



--problem 4
reverse-++-dist : ∀ {A : Set} (xs ys : List A)
                → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-dist [] ys = sym (++-identityʳ (reverse ys))
reverse-++-dist (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨ refl ⟩
    reverse (xs ++ ys) ++ (x ∷ [])
  ≡⟨ cong (_++ (x ∷ [])) (reverse-++-dist xs ys) ⟩
    (reverse ys ++ reverse xs) ++ (x ∷ [])
  ≡⟨ ++-assoc (reverse ys) (reverse xs) (x ∷ []) ⟩
    reverse ys ++ (reverse xs ++ (x ∷ []))
  ≡⟨ refl ⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎



--problem 5
reverse-involution : ∀ {A : Set} (xs : List A)
                   → reverse (reverse xs) ≡ xs
reverse-involution [] = refl
reverse-involution (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨ refl ⟩
    reverse ((reverse xs) ++ (x ∷ []))
  ≡⟨ reverse-++-dist (reverse xs) (x ∷ []) ⟩
    reverse (x ∷ []) ++ reverse (reverse xs)
  ≡⟨ refl ⟩
    (x ∷ []) ++ reverse (reverse xs)
  ≡⟨ cong ((x ∷ []) ++_) (reverse-involution xs) ⟩
    (x ∷ []) ++ xs
  ≡⟨ refl ⟩
    x ∷ xs
  ∎



reverse-acc : {A : Set} → List A → List A → List A
reverse-acc [] acc = acc
reverse-acc (x ∷ xs) acc = reverse-acc xs (x ∷ acc)

reverse-fast : {A : Set} → List A → List A
reverse-fast xs = reverse-acc xs []



lemma-reverse-acc : ∀ {A : Set} (xs acc : List A)
                  → reverse-acc xs acc ≡ (reverse xs) ++ acc
lemma-reverse-acc [] acc = refl
lemma-reverse-acc (x ∷ xs) acc =
  begin
    reverse-acc (x ∷ xs) acc
  ≡⟨ refl ⟩
    reverse-acc xs (x ∷ acc)
  ≡⟨ lemma-reverse-acc xs (x ∷ acc) ⟩
    reverse xs ++ (x ∷ acc)
  ≡⟨ refl ⟩
    (reverse xs) ++ ((x ∷ []) ++ acc)
  ≡⟨ sym (++-assoc (reverse xs) (x ∷ []) acc) ⟩
    ((reverse xs) ++ (x ∷ [])) ++ acc
  ≡⟨ cong (_++ acc) refl ⟩
    reverse (x ∷ xs) ++ acc
  ∎



reverse-fast≡reverse : ∀ {A : Set} (xs : List A)
                     → reverse-fast xs ≡ reverse xs
reverse-fast≡reverse [] = refl
reverse-fast≡reverse (x ∷ xs) =
  begin
    reverse-fast (x ∷ xs)
  ≡⟨ refl ⟩
    reverse-acc (x ∷ xs) []
  ≡⟨ refl ⟩
    reverse-acc xs (x ∷ [])
  ≡⟨ lemma-reverse-acc xs (x ∷ []) ⟩
    (reverse xs) ++ (x ∷ [])
  ≡⟨ refl ⟩
    reverse (x ∷ xs)
  ∎



--problem 6
reverse-fast-involution : ∀ {A : Set} (xs : List A)
                        → reverse-fast (reverse-fast xs) ≡ xs
reverse-fast-involution xs =
  begin
    reverse-fast (reverse-fast xs)
  ≡⟨ cong reverse-fast (reverse-fast≡reverse xs) ⟩
    reverse-fast (reverse xs)
  ≡⟨ reverse-fast≡reverse (reverse xs) ⟩
    reverse (reverse xs)
  ≡⟨ reverse-involution xs ⟩
    xs
  ∎



filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs



filter-true : ∀ {A : Set} (p : A → Bool) (x : A) (xs : List A)
            → p x ≡ true → filter p (x ∷ xs) ≡ x ∷ filter p xs
filter-true p x xs px≡true rewrite px≡true = refl

--problem 7
filter-idempotent : ∀ {A : Set} (p : A → Bool) (xs : List A)
                  → filter p (filter p xs) ≡ filter p xs
filter-idempotent p [] = refl
filter-idempotent p (x ∷ xs) with (p x) in px
filter-idempotent p (x ∷ xs)    | false = filter-idempotent p xs
filter-idempotent p (x ∷ xs)    | true =
  begin
    filter p (x ∷ (filter p xs))
  ≡⟨ filter-true p x (filter p xs) px ⟩
    x ∷ filter p (filter p xs)
  ≡⟨ cong (x ∷_) (filter-idempotent p xs) ⟩
    x ∷ (filter p xs)
  ∎



--problem 8
filter-++-dist : ∀ {A : Set} (p : A → Bool) (xs ys : List A)
               → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
filter-++-dist p [] ys = refl
filter-++-dist p (x ∷ xs) ys with (p x)
... | false = filter-++-dist p xs ys
... | true  = cong (x ∷_) (filter-++-dist p xs ys)



--problem 9
any-true-implies-Any : ∀ {A : Set} (p : A → Bool) (xs : List A)
                     → any p xs ≡ true → Any (λ x → p x ≡ true) xs
any-true-implies-Any p (x ∷ xs) any-p with (p x) in px
... | false = there (any-true-implies-Any p xs any-p)
... | true = here px



--problem 10
decide-membership : ∀ {A : Set} (dec-eq : (x y : A) → Dec (x ≡ y)) (target : A) (xs : List A)
                  → Dec (Any (_≡_ target) xs)
decide-membership dec-eq target [] = no (λ ())
decide-membership dec-eq target (x ∷ xs) with dec-eq target x
decide-membership dec-eq target (x ∷ xs) | yes t = yes (here t)
decide-membership dec-eq target (x ∷ xs) | no ¬t with decide-membership dec-eq target xs
decide-membership dec-eq target (x ∷ xs) | no ¬t | yes u = yes (there u)
decide-membership dec-eq target (x ∷ xs) | no ¬t | no ¬u = no λ { (here px) → ¬t px ; (there v) → ¬u v}

--just changing with dec-eq target x into with dec-eq x target
decide-membership₁ : ∀ {A : Set} (dec-eq : (x y : A) → Dec (x ≡ y)) (target : A) (xs : List A)
                   → Dec (Any (_≡_ target) xs)
decide-membership₁ dec-eq target [] = no (λ ())
decide-membership₁ dec-eq target (x ∷ xs) with dec-eq x target
decide-membership₁ dec-eq target (x ∷ xs) | yes t = yes (here (sym t))
decide-membership₁ dec-eq target (x ∷ xs) | no ¬t with decide-membership₁ dec-eq target xs
decide-membership₁ dec-eq target (x ∷ xs) | no ¬t | yes u = yes (there u)
decide-membership₁ dec-eq target (x ∷ xs) | no ¬t | no ¬u = no λ { (here px) → ¬t (sym px) ; (there v) → ¬u v}



insert : {A B : Set} → A → B → List (A × B) → List (A × B)
insert k v store = (k , v) ∷ store

lookup : {A B : Set} → (dec-eq : (x y : A) → Dec (x ≡ y)) → A → List (A × B) → Maybe B
lookup dec-eq target [] = nothing
lookup dec-eq target ((k , v) ∷ store) with (dec-eq target k)
... | yes t = just v
... | no ¬t = lookup dec-eq target store

--problem 11
lookup-after-insert : ∀ {A B : Set} (k : A) (v : B) (store : List (A × B))
                    → (dec-eq : (x y : A) → Dec (x ≡ y))
                    → lookup dec-eq k (insert k v store) ≡ just v
lookup-after-insert k v store dec-eq with dec-eq k k
... | yes k≡k = refl
... | no ¬k≡k = ⊥-elim (¬k≡k refl)


--problem 12
lookup-shadowed : ∀ {A B : Set} (k : A) (v1 v2 : B) (store : List (A × B))
                → (dec-eq : (x y : A) → Dec (x ≡ y))
                → lookup dec-eq k (insert k v2 (insert k v1 store)) ≡ just v2
lookup-shadowed k v1 v2 store dec-eq with dec-eq k k
... | yes k≡k = refl
... | no ¬k≡k = ⊥-elim (¬k≡k refl)



--problem 12-2
lookup-shadowed-distinct : ∀ {A B : Set} (k1 k2 : A) (v1 v2 : B) (store : List (A × B))
                         → (dec-eq : (x y : A) → Dec (x ≡ y))
                         → k1 ≢ k2
                         → lookup dec-eq k1 (insert k2 v2 (insert k1 v1 store)) ≡ just v1
lookup-shadowed-distinct k1 k2 v1 v2 store dec-eq distinct with dec-eq k1 k2
... | yes k1≡k2 = ⊥-elim (distinct k1≡k2)
... | no ¬k1≡k2 with dec-eq k1 k1
...             | yes k1≡k1 = refl
...             | no ¬k1≡k1 = ⊥-elim (¬k1≡k1 refl)



--problem 13
vec-lookup-safe : {A : Set} {n : ℕ} (i : Fin n) (vec : Vec A n) → A
vec-lookup-safe zeroᶠ (v ∷ᵛ vec) = v
vec-lookup-safe (sucᶠ i) (v ∷ᵛ vec) = vec-lookup-safe i vec



--problem 14
take-drop-invariant : ∀ {A : Set} (n : ℕ) (xs : List A)
                    → take n xs ++ drop n xs ≡ xs
take-drop-invariant zero [] = refl
take-drop-invariant (suc n) [] = refl
take-drop-invariant zero (x ∷ xs) = refl
take-drop-invariant (suc n) (x ∷ xs) =
  begin
    take (suc n) (x ∷ xs) ++ drop (suc n) (x ∷ xs)
  ≡⟨ refl ⟩
    (x ∷ take n xs) ++ (drop n xs)
  ≡⟨ refl ⟩
    x ∷ (take n xs ++ drop n xs)
  ≡⟨ cong (x ∷_) (take-drop-invariant n xs) ⟩
    x ∷ xs
  ∎



encode-rle-helper : (ncur cur : ℕ) → (xs : List ℕ) → List (ℕ × ℕ)
encode-rle-helper ncur cur [] = (ncur , cur) ∷ []
encode-rle-helper ncur cur (x ∷ xs) with cur ≟ x
... | yes _ = encode-rle-helper (suc ncur) cur xs
... | no _ = (ncur , cur) ∷ encode-rle-helper 1 x xs

encode-rle : List ℕ → List (ℕ × ℕ)
encode-rle [] = []
encode-rle (x ∷ xs) = encode-rle-helper 1 x xs

decode-rle : List (ℕ × ℕ) → List ℕ
decode-rle [] = []
decode-rle ((zero , cur) ∷ xs) = decode-rle xs
decode-rle ((suc ncur , cur) ∷ xs) = cur ∷ decode-rle ((ncur , cur) ∷ xs)

lemma-rle : ∀ (ncur cur : ℕ) (xs : List ℕ)
          → decode-rle (encode-rle-helper (suc ncur) cur xs)
          ≡ cur ∷ decode-rle (encode-rle-helper ncur cur xs)
lemma-rle ncur cur [] = refl
lemma-rle ncur cur (x ∷ xs) with cur ≟ x
... | yes cur≡x =
  begin
    decode-rle (encode-rle-helper (suc (suc ncur)) cur xs)
  ≡⟨ lemma-rle (suc ncur) cur xs ⟩
    cur ∷ decode-rle (encode-rle-helper (suc ncur) cur xs)
  ∎
... | no ¬cur≡x = refl

lemma-rle₂ : ∀ (cur : ℕ) (xs : List ℕ)
           → decode-rle (encode-rle-helper 0 cur xs)
           ≡ decode-rle (encode-rle xs)
lemma-rle₂ cur [] = refl
lemma-rle₂ cur (x ∷ xs) with cur ≟ x
... | yes cur≡x =
  begin
    decode-rle (encode-rle-helper 1 cur xs)
  ≡⟨ cong (λ z → decode-rle (encode-rle-helper 1 z xs)) cur≡x ⟩
    decode-rle (encode-rle-helper 1 x xs)
  ∎
... | no ¬cur≡x = refl

--problem 15
rle-roundtrip : ∀ (xs : List ℕ)
              → decode-rle (encode-rle xs) ≡ xs
rle-roundtrip [] = refl
rle-roundtrip (x ∷ xs) =
  begin
    decode-rle (encode-rle (x ∷ xs))
  ≡⟨ refl ⟩
    decode-rle (encode-rle-helper 1 x xs)
  ≡⟨ lemma-rle 0 x xs ⟩
    x ∷ decode-rle (encode-rle-helper 0 x xs)
  ≡⟨ cong (x ∷_) (lemma-rle₂ x xs) ⟩
    x ∷ decode-rle (encode-rle xs)
  ≡⟨ cong (x ∷_) (rle-roundtrip xs) ⟩
    x ∷ xs
  ∎
