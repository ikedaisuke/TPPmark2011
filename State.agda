module State where

-- http://staff.aist.go.jp/reynald.affeldt/tpp2011/garrigue_candy.v

open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

open import Half
open import MinMaxLe

-- I changed the definition of State to Vec with length
-- because to prove the lemma 'length-stable'
data State : (len : ℕ) -> Set where
  last : (n : ℕ) -> State (suc zero)
  cons : ∀ {len} (n : ℕ) -> (xs : State len) -> State (suc len)

hd : ∀ {len} (s : State len) -> ℕ
hd (last n) = n
hd (cons n _) = n

length : ∀ {len} (s : State len) -> ℕ
length (last n) = suc zero
length (cons {len} n xs) = suc len

next : ∀ {len} (fst : ℕ) -> (s : State len) -> State len
next fst (last n)    = last (half (n + fst))
next fst (cons n xs) = cons (half (n + hd xs)) (next fst xs)

next-state : ∀ {len} -> State len -> State len
next-state s = next (hd s) s

nth-state : ∀ {len} (n : ℕ) -> (s : State len) -> State len
nth-state zero s = s
nth-state (suc n) s = nth-state n (next-state s)

nth-state-plus : ∀ {len} m n s -> 
  nth-state {len} (m + n) s ≡ nth-state {len} n (nth-state m s)
nth-state-plus zero n s = refl
nth-state-plus (suc m) zero s 
  = cong (λ x -> nth-state x s) (+-comm (suc m) zero)
nth-state-plus (suc m) (suc n) s = begin
  nth-state (suc m + suc n) s
  ≡⟨ nth-state-plus m (suc n) (next (hd s) s) ⟩
  nth-state n
    (next (hd (nth-state m (next (hd s) s)))
     (nth-state m (next (hd s) s)))
  ≡⟨ refl ⟩
  nth-state (suc n) (nth-state (suc m) s)
  ∎
  where open ≡-Reasoning

-- lemma: length-stable
length-stable : ∀ {len} s -> length (next-state {len} s) ≡ length s
length-stable (last n) = refl
length-stable (cons n xs) = refl

-- lemma: length-stable-nth
length-stable-nth : ∀ {len} n s -> 
  length (nth-state {len} n s) ≡ length {len} s
length-stable-nth zero s = refl
length-stable-nth (suc n) (last m) = begin
  length (nth-state n (last (half (m + m))))
    ≡⟨ length-stable-nth n (last (half (m + m))) ⟩
  length (last m) ≡⟨ refl ⟩
  suc zero
  ∎
  where open ≡-Reasoning
length-stable-nth (suc n) (cons {len} m xs) = begin
  length (nth-state (suc n) (cons m xs)) ≡⟨ refl ⟩
  length (nth-state n (next-state (cons m xs)))
    ≡⟨ length-stable-nth n (cons (half (m + hd xs)) 
                           (next m xs)) ⟩
  suc len ≡⟨ refl ⟩
  length (cons {len} m xs)
  ∎
  where open ≡-Reasoning

-- the max function on state
max : ∀ {len} -> State len -> ℕ
max (last n) = n
max (cons n xs) = n ⊔ max xs

-- the min function on state
min : ∀ {len} -> State len -> ℕ
min (last n) = n
min (cons n xs) = n ⊓ min xs

-- lemma: le-min-max
le-min-max : ∀ {len} s -> min {len} s ≤ max s
le-min-max (last n) = ≤-refl n
le-min-max (cons n xs) = begin
  n ⊓ min xs ≤⟨ ≤-elim-min-left n (min xs) ⟩
  min xs ≤⟨ le-min-max xs ⟩
  max xs ≤⟨ ≤-add-max-right (max xs) n ⟩
  max xs ⊔ n ≤⟨ ≤-max-comm (max xs) n ⟩
  n ⊔ max xs 
  ∎
  where open ≤-Reasoning

-- lemma: le-min-hd
le-min-hd : ∀ {len} s -> min {len} s ≤ hd s
le-min-hd (last n) = ≤-refl n
le-min-hd (cons n xs) = begin
  n ⊓ min xs ≤⟨ ≤-min-comm n (min xs) ⟩
  min xs ⊓ n ≤⟨ ≤-elim-min-left (min xs) n ⟩
  n
  ∎
  where open ≤-Reasoning

-- lemma: le-hd-max
le-hd-max : ∀ {len} s -> hd s ≤ max {len} s
le-hd-max (last n) = ≤-refl n
le-hd-max (cons n xs) = begin
  n ≤⟨ ≤-add-max-right n (max xs) ⟩
  n ⊔ max xs
  ∎
  where open ≤-Reasoning

diff : ∀ {len} -> State len -> ℕ
diff s = max s ∸ min s

-- the num function
num : ∀ {len} (n : ℕ) -> (s : State len) -> ℕ
num n (last m) with m ≟ n
... | yes p = suc zero
... | no ¬p = zero
num n (cons m xs) with m ≟ n
... | yes p = suc (num n xs)
... | no ¬p = num n xs

≤-length : ∀ {len} -> (s : State len) -> length s ≤ len
≤-length (last n) = ≤-refl (suc zero)
≤-length (cons {len} n xs) = ≤-refl (suc len)

-- lemma: le-num-length
le-num-length : ∀ {len} n s -> num {len} n s ≤ length s
le-num-length n (last m) with m ≟ n
... | yes p = ≤-refl (suc zero)
... | no ¬p = z≤n
le-num-length n (cons {len} m xs) with m ≟ n
... | yes p = begin
              suc (num n xs) ≤⟨ ≤-suc-suc (le-num-length n xs) ⟩
              suc (length xs) ≤⟨ ≤-suc-suc (≤-length xs) ⟩
              suc len
              ∎
              where open ≤-Reasoning
... | no ¬p = begin
              num n xs ≤⟨ le-num-length n xs ⟩
              length xs ≤⟨ ≤-length xs ⟩
              len ≤⟨ ≤-suc len ⟩
              suc len
              ∎
              where open ≤-Reasoning

≤-max-next-grows : ∀ {len} m n xs -> m ≤ n -> 
                   max {len} (next m xs) ≤ max (next n xs)
≤-max-next-grows zero zero xs p 
  = ≤-refl (max (next zero xs))
≤-max-next-grows zero (suc n) (last x) p 
  = half-grows (x + zero) (x + suc n) 
               (≤-plus-act-right x zero (suc n) p)
≤-max-next-grows zero (suc n) (cons x xs) p 
  = ≤-max-act-right (half (x + hd xs)) (max (next zero xs)) 
                    (max (next (suc n) xs)) 
                    (≤-max-next-grows zero (suc n) xs p)
≤-max-next-grows (suc m) zero xs ()
≤-max-next-grows (suc m) (suc n) (last x) p 
  = half-grows (x + suc m) (x + suc n) 
               (≤-plus-act-right x (suc m) (suc n) p)
≤-max-next-grows (suc m) (suc n) (cons x xs) p 
  = ≤-max-act-right (half (x + hd xs)) (max (next (suc m) xs)) 
                    (max (next (suc n) xs)) 
                    (≤-max-next-grows (suc m) (suc n) xs p)

≤-max-elim-left : ∀ x y -> y ≤ x -> x ⊔ y ≤ x
≤-max-elim-left zero y p = p
≤-max-elim-left (suc n) zero p = ≤-refl (suc n)
≤-max-elim-left (suc m) (suc n) p = begin
  suc (m ⊔ n) ≤⟨ ≤-refl (suc (m ⊔ n)) ⟩
  suc m ⊔ suc n 
    ≤⟨ ≤-suc-suc (≤-max-elim-left m n (≤-pred p)) ⟩
  suc m 
  ∎
  where open ≤-Reasoning

≤-max-max-elim-right : ∀ x y z -> z ≤ y -> x ⊔ y ⊔ z ≤ x ⊔ y
≤-max-max-elim-right zero zero z p = p
≤-max-max-elim-right zero (suc n) zero p = ≤-refl (suc n)
≤-max-max-elim-right zero (suc n) (suc z) p 
  = ≤-suc-suc (≤-max-elim-left n z (≤-pred p))
≤-max-max-elim-right (suc m) zero zero p 
  = ≤-refl (suc m)
≤-max-max-elim-right (suc m) zero (suc z) ()
≤-max-max-elim-right (suc m) (suc n) zero p 
  = ≤-refl (suc (m ⊔ n))
≤-max-max-elim-right (suc m) (suc n) (suc z) p = begin
  suc (m ⊔ n ⊔ z) 
    ≤⟨ ≤-suc-suc (≤-max-max-elim-right m n z (≤-pred p)) ⟩
  suc (m ⊔ n)
  ∎
  where open ≤-Reasoning

≤-next-cons : ∀ {len} n xs -> max {len} (next n xs) ≤ n ⊔ max xs
≤-next-cons zero (last n) 
  = half-exact-le (n + zero) n (≤-plus-comm-left zero n n (≤-refl n))
≤-next-cons zero (cons n xs) = begin
  half (n + hd xs) ⊔ max (next zero xs) 
    ≤⟨ ≤-max-act-left (half (n + hd xs)) (n ⊔ hd xs) 
          (max (next zero xs)) (half-max n (hd xs)) ⟩
  n ⊔ hd xs ⊔ max (next zero xs) 
    ≤⟨ ≤-max-act-left (n ⊔ hd xs) (n ⊔ max xs) 
        (max (next zero xs)) 
        (≤-max-act-right n (hd xs) (max xs) (le-hd-max xs)) ⟩
  n ⊔ max xs ⊔ max (next zero xs) 
    ≤⟨ ≤-max-max-elim-right n (max xs) (max (next zero xs)) (≤-next-cons zero xs) ⟩
  n ⊔ max xs
  ∎
  where open ≤-Reasoning
≤-next-cons (suc m) (last n) = begin
  half (n + suc m) ≤⟨ half-max n (suc m) ⟩
  n ⊔ suc m ≤⟨ ≤-max-comm n (suc m) ⟩
  suc m ⊔ n 
  ∎
  where open ≤-Reasoning
≤-next-cons (suc m) (cons n xs) = begin
  half (n + hd xs) ⊔ max (next (suc m) xs) 
    ≤⟨ ≤-max-act-left (half (n + hd xs)) (n ⊔ hd xs) 
        (max (next (suc m) xs)) (half-max n (hd xs)) ⟩
  n ⊔ hd xs ⊔ max (next (suc m) xs) 
    ≤⟨ ≤-max-act-left (n ⊔ hd xs) (n ⊔ max xs) 
        (max (next (suc m) xs))
        (≤-max-act-right n (hd xs) (max xs) (le-hd-max xs)) ⟩
  n ⊔ max xs ⊔ max (next (suc m) xs) 
    ≤⟨ ≤-max-act-right (n ⊔ max xs) 
        (max (next (suc m) xs)) (suc m ⊔ max xs) 
        (≤-next-cons (suc m) xs) ⟩
  n ⊔ max xs ⊔ (suc m ⊔ max xs) 
    ≤⟨ ≤-max-assoc-left n (max xs) (suc m ⊔ max xs) ⟩
  n ⊔ (max xs ⊔ (suc m ⊔ max xs)) 
    ≤⟨ ≤-max-act-right n (max xs ⊔ (suc m ⊔ max xs)) 
        (max xs ⊔ suc m ⊔ max xs) 
        (≤-max-assoc-right (max xs) (suc m) (max xs)) ⟩
  n ⊔ ((max xs ⊔ suc m) ⊔ max xs) 
    ≤⟨ ≤-max-act-right n (max xs ⊔ suc m ⊔ max xs) 
        (suc m ⊔ max xs ⊔ max xs) 
        (≤-max-act-left (max xs ⊔ suc m) 
          (suc m ⊔ max xs) (max xs) 
          (≤-max-comm (max xs) (suc m))) ⟩
  n ⊔ ((suc m ⊔ max xs) ⊔ max xs) 
    ≤⟨ ≤-max-act-right n (suc m ⊔ max xs ⊔ max xs) 
        (suc m ⊔ (max xs ⊔ max xs)) 
        (≤-max-assoc-left (suc m) (max xs) (max xs)) ⟩
  n ⊔ (suc m ⊔ (max xs ⊔ max xs)) 
    ≤⟨ ≤-max-act-right n (suc m ⊔ (max xs ⊔ max xs)) 
         (suc m ⊔ max xs) (≤-max-act-right (suc m) 
           (max xs ⊔ max xs) (max xs) 
           (≤-max-max-elim-right zero (max xs) (max xs) 
              (≤-refl (max xs)))) ⟩
  n ⊔ (suc m ⊔ max xs) 
    ≤⟨ ≤-max-assoc-right n (suc m) (max xs) ⟩
  (n ⊔ suc m) ⊔ max xs 
     ≤⟨ ≤-max-act-left (n ⊔ suc m) (suc m ⊔ n) (max xs) 
         (≤-max-comm n (suc m)) ⟩
  (suc m ⊔ n) ⊔ max xs 
     ≤⟨ ≤-max-assoc-left (suc m) n (max xs) ⟩
  suc m ⊔ (n ⊔ max xs)  
  ∎
  where open ≤-Reasoning

-- lemma: max-decr
max-decr : ∀ {len} s -> max {len} (next-state s) ≤ max s
max-decr (last n) 
  = ≤-refl-≡ (half (n + n)) n (half-double n)
max-decr (cons n xs) = begin
  half (n + hd xs) ⊔ max (next n xs) 
    ≤⟨ ≤-max-act-left (half (n + hd xs)) (half (n + max xs)) 
                       (max (next n xs)) 
                       (half-grows (n + hd xs) (n + max xs) 
                       (≤-plus-act-right n (hd xs) (max xs) 
                                           (le-hd-max xs))) ⟩
  half (n + max xs) ⊔ max (next n xs) 
    ≤⟨ ≤-max-act-left (half (n + max xs)) (n ⊔ max xs) 
                       (max (next n xs)) (half-max n (max xs)) ⟩
  n ⊔ max xs ⊔ max (next n xs) 
    ≤⟨ ≤-max-assoc-left n (max xs) (max (next n xs)) ⟩ 
  n ⊔ (max xs ⊔ max (next n xs)) 
    ≤⟨ ≤-max-act-right n (max xs ⊔ max (next n xs)) 
        (max xs ⊔ (n ⊔ max xs)) 
        (≤-max-act-right (max xs) (max (next n xs)) 
          (n ⊔ max xs) (≤-next-cons n xs)) ⟩
  n ⊔ (max xs ⊔ (n ⊔ max xs)) 
    ≤⟨ ≤-max-act-right n (max xs ⊔ (n ⊔ max xs)) 
        (max xs ⊔ n ⊔ max xs) 
        (≤-max-assoc-right (max xs) n (max xs)) ⟩
  n ⊔ ((max xs ⊔ n) ⊔ max xs) 
    ≤⟨ ≤-max-act-right n (max xs ⊔ n ⊔ max xs) 
        (n ⊔ max xs ⊔ max xs) 
          (≤-max-act-left (max xs ⊔ n) (n ⊔ max xs) 
            (max xs) (≤-max-comm (max xs) n)) ⟩
  n ⊔ (n ⊔ max xs ⊔ max xs) 
    ≤⟨ ≤-max-act-right n (n ⊔ max xs ⊔ max xs) 
        (n ⊔ (max xs ⊔ max xs)) 
         (≤-max-assoc-left n (max xs) (max xs)) ⟩
  n ⊔ (n ⊔ (max xs ⊔ max xs)) 
    ≤⟨ ≤-max-act-right n (n ⊔ (max xs ⊔ max xs)) 
         (n ⊔ max xs) 
         (≤-max-act-right n (max xs ⊔ max xs) (max xs) 
         (≤-max-max-elim-right zero (max xs) (max xs) 
           (≤-refl (max xs)))) ⟩
  n ⊔ (n ⊔ max xs) 
    ≤⟨ ≤-max-assoc-right n n (max xs) ⟩
  (n ⊔ n) ⊔ max xs 
    ≤⟨ ≤-max-act-left (n ⊔ n) n (max xs) 
        (≤-max-max-elim-right zero n n (≤-refl n)) ⟩
  n ⊔ max xs
  ∎
  where open ≤-Reasoning
