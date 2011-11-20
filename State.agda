module State where

-- http://staff.aist.go.jp/reynald.affeldt/tpp2011/garrigue_candy.v

open import Data.Empty
open import Data.Nat
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

≤-next-le-max : ∀ {len} n xs -> max {len} (next n xs) ≤ n ⊔ max xs
≤-next-le-max zero (last n) 
  = half-exact-le (n + zero) n (≤-plus-comm-left zero n n (≤-refl n))
≤-next-le-max zero (cons n xs) = begin
  half (n + hd xs) ⊔ max (next zero xs) 
    ≤⟨ ≤-max-act-left (half (n + hd xs)) (n ⊔ hd xs) 
          (max (next zero xs)) (half-max n (hd xs)) ⟩
  n ⊔ hd xs ⊔ max (next zero xs) 
    ≤⟨ ≤-max-act-left (n ⊔ hd xs) (n ⊔ max xs) 
        (max (next zero xs)) 
        (≤-max-act-right n (hd xs) (max xs) (le-hd-max xs)) ⟩
  n ⊔ max xs ⊔ max (next zero xs) 
    ≤⟨ ≤-max-max-elim-right n (max xs) (max (next zero xs)) (≤-next-le-max zero xs) ⟩
  n ⊔ max xs
  ∎
  where open ≤-Reasoning
≤-next-le-max (suc m) (last n) = begin
  half (n + suc m) ≤⟨ half-max n (suc m) ⟩
  n ⊔ suc m ≤⟨ ≤-max-comm n (suc m) ⟩
  suc m ⊔ n 
  ∎
  where open ≤-Reasoning
≤-next-le-max (suc m) (cons n xs) = begin
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
        (≤-next-le-max (suc m) xs) ⟩
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

≤-min-le-next : ∀ {len} n xs -> n ⊓ min {len} xs ≤ min (next n xs)
≤-min-le-next zero xs = z≤n
≤-min-le-next (suc n) (last x) = begin
  suc n ⊓ x ≤⟨ ≤-min-comm (suc n) x ⟩
  x ⊓ suc n ≤⟨ half-min x (suc n) ⟩
  half (x + suc n)
  ∎
  where open ≤-Reasoning
≤-min-le-next (suc m) (cons n xs) = begin
  suc m ⊓ (n ⊓ min xs) 
    ≤⟨ ≤-min-assoc-right (suc m) n (min xs) ⟩
  suc m ⊓ n ⊓ min xs 
    ≤⟨ ≤-min-act-left (suc m ⊓ n) (n ⊓ suc m) (min xs) 
        (≤-min-comm (suc m) n)  ⟩
  n ⊓ suc m ⊓ min xs 
    ≤⟨ ≤-min-assoc-left n (suc m) (min xs) ⟩
  n ⊓ (suc m ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (suc m ⊓ min xs) 
        (suc m ⊓ (min xs ⊓ min xs)) 
        (≤-min-act-right (suc m) (min xs) (min xs ⊓ min xs) 
          (≤-min-elim-left (min xs) (min xs) 
            (≤-refl (min xs))))  ⟩
  n ⊓ (suc m ⊓ (min xs ⊓ min xs)) 
    ≤⟨ ≤-min-act-right n (suc m ⊓ (min xs ⊓ min xs)) 
         (suc m ⊓ min xs ⊓ min xs) 
         (≤-min-assoc-right (suc m) (min xs) (min xs)) ⟩
  n ⊓ (suc m ⊓ min xs ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (suc m ⊓ min xs ⊓ min xs) 
       (min xs ⊓ suc m ⊓ min xs) 
       (≤-min-act-left (suc m ⊓ min xs) (min xs ⊓ suc m)
       (min xs) 
         (≤-min-comm (suc m) (min xs))) ⟩
  n ⊓ (min xs ⊓ suc m ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (min xs ⊓ suc m ⊓ min xs) 
         (min xs ⊓ (suc m ⊓ min xs)) 
         (≤-min-assoc-left (min xs) (suc m) (min xs)) ⟩
  n ⊓ (min xs ⊓ (suc m ⊓ min xs)) 
    ≤⟨ ≤-min-assoc-right n (min xs) (suc m ⊓ min xs) ⟩
  n ⊓ min xs ⊓ (suc m ⊓ min xs) 
    ≤⟨ ≤-min-act-right (n ⊓ min xs) (suc m ⊓ min xs) 
       (min (next (suc m) xs)) (≤-min-le-next (suc m) xs) ⟩
  n ⊓ min xs ⊓ min (next (suc m) xs) 
    ≤⟨ ≤-min-act-left (n ⊓ min xs) (n ⊓ hd xs) 
        (min (next (suc m) xs)) 
          (≤-min-act-right n (min xs) (hd xs) (le-min-hd xs)) ⟩
  n ⊓ hd xs ⊓ min (next (suc m) xs)
    ≤⟨ ≤-min-act-left (n ⊓ hd xs) (half (n + hd xs)) 
        (min (next (suc m) xs)) (half-min n (hd xs)) ⟩
  half (n + hd xs) ⊓ min (next (suc m) xs)
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
          (n ⊔ max xs) (≤-next-le-max n xs)) ⟩
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

-- lemma: min-incr
min-incr : ∀ {len} s -> min {len} s ≤ min (next-state s)
min-incr (last n) 
  = ≤-refl-≡ n (half (n + n)) (sym (half-double n))
min-incr (cons n xs) = begin
  n ⊓ min xs 
    ≤⟨ ≤-min-act-left n (n ⊓ n) (min xs) 
       (≤-min-elim-left n n (≤-refl n)) ⟩
  n ⊓ n ⊓ min xs 
    ≤⟨ ≤-min-assoc-left n n (min xs) ⟩ 
  n ⊓ (n ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (n ⊓ min xs) 
        (n ⊓ (min xs ⊓ min xs)) 
        (≤-min-act-right n (min xs) (min xs ⊓ min xs) 
        (≤-min-elim-left (min xs) (min xs) 
        (≤-refl (min xs)))) ⟩ 
  n ⊓ (n ⊓ (min xs ⊓ min xs)) 
    ≤⟨ ≤-min-act-right n (n ⊓ (min xs ⊓ min xs)) 
        (n ⊓ min xs ⊓ min xs) 
        (≤-min-assoc-right n (min xs) (min xs)) ⟩ 
  n ⊓ (n ⊓ min xs ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (n ⊓ min xs ⊓ min xs) 
        (min xs ⊓ n ⊓ min xs) 
        (≤-min-act-left (n ⊓ min xs) (min xs ⊓ n) 
          (min xs) (≤-min-comm n (min xs))) ⟩ 
  n ⊓ (min xs ⊓ n ⊓ min xs) 
    ≤⟨ ≤-min-act-right n (min xs ⊓ n ⊓ min xs) 
        (min xs ⊓ (n ⊓ min xs))
        (≤-min-assoc-left (min xs) n (min xs)) ⟩ 
  n ⊓ (min xs ⊓ (n ⊓ min xs)) 
    ≤⟨ ≤-min-act-right n (min xs ⊓ (n ⊓ min xs)) 
        (min xs ⊓ min (next n xs)) 
        (≤-min-act-right (min xs) (n ⊓ min xs) 
        (min (next n xs)) 
        ( ≤-min-le-next n xs)) ⟩ 
  n ⊓ (min xs ⊓ min (next n xs)) 
    ≤⟨ ≤-min-assoc-right n (min xs) (min (next n xs)) ⟩
  n ⊓ min xs ⊓ min (next n xs) 
    ≤⟨ ≤-min-act-left (n ⊓ min xs) 
        (half (n + min xs)) 
        (min (next n xs)) 
        (half-min n (min xs)) ⟩
  half (n + min xs) ⊓ min (next n xs) 
    ≤⟨ ≤-min-act-left (half (n + min xs)) 
        (half (n + hd xs)) (min (next n xs)) 
        (half-grows (n + min xs) (n + hd xs) 
        (≤-plus-act-right n (min xs) (hd xs) 
          (le-min-hd xs))) ⟩
  half (n + hd xs) ⊓ min (next n xs)
  ∎
  where open ≤-Reasoning

-- use half-loop, half-grows
-- lemma: min-num-stable
min-num-stable : ∀ {len} x y s ->
  x ≤ min {len} s -> x ≤ y -> num x (next y s) ≤ num x s
min-num-stable zero zero (last zero) p q = s≤s q
min-num-stable zero zero (last (suc z)) p q 
  with half (suc (z + 0)) ≟ 0
... | yes r = helper
  where open ≤-Reasoning
        helper : suc zero ≤ zero -- unsat
        helper = begin
          suc zero ≤⟨ half-one-le z ⟩
          half (suc z) 
            ≤⟨ ≤-half-≡ (suc z) (suc (z + zero)) 
                (sym (≡-plus-zero-right (suc z))) ⟩
          half (suc (z + zero)) 
            ≤⟨ ≤-refl-≡ (half (suc (z + zero))) zero r ⟩
          zero
          ∎
... | no ¬r = q
min-num-stable zero (suc n) (last zero) p q 
  with half (suc n) ≟ 0
... | yes r = s≤s p
... | no ¬r = z≤n
min-num-stable zero (suc n) (last (suc z)) p q 
  with half (suc (z + suc n)) ≟ 0
... | yes r = helper
  where open ≤-Reasoning
        helper : suc zero ≤ zero -- unsat
        helper = begin
          suc zero ≤⟨ half-one-le (z + suc n) ⟩
          half (suc (z + suc n)) 
            ≤⟨ ≤-refl-≡ (half (suc (z + suc n))) zero r ⟩
          zero
          ∎
... | no ¬r = z≤n
min-num-stable (suc m) zero (last z) p ()
min-num-stable (suc m) (suc n) (last zero) () q 
min-num-stable (suc m) (suc n) (last (suc z)) p q
  with half (suc (z + suc n)) ≟ suc m | z ≟ m | suc z ≟ suc m
... | yes r | yes s | yes t = s≤s z≤n
... | yes r | yes s | no ¬t 
  = ⊥-elim (¬t (cong suc s))
... | yes r | no ¬s | yes t = s≤s z≤n
... | yes r | no ¬s | no ¬t = {!!} -- unsat GAMEOVER
... | no ¬r | _     | _ = z≤n
min-num-stable zero zero (cons zero xs) p q = {!!}
min-num-stable zero zero (cons (suc n) xs) p q = {!!}
min-num-stable zero (suc n) (cons zero xs) p q = {!!}
min-num-stable zero (suc n) (cons (suc z) xs) p q = {!!}
min-num-stable (suc m) zero (cons x xs) p ()
min-num-stable (suc m) (suc n) (cons zero xs) p q = {!!}
min-num-stable (suc m) (suc n) (cons (suc z) xs) p q 
  with half (suc (z + hd xs)) ≟ suc m | z ≟ m | suc z ≟ suc m
... | yes r | yes s | yes t = {!!}
... | yes r | yes s | no ¬t 
  = ⊥-elim (¬t (cong suc s))
... | yes r | no ¬s | yes t 
  = ⊥-elim (¬s (cong pred t))
... | yes r | no ¬s | no ¬t = {!!}
... | no ¬r | yes s | yes t = {!!}
... | no ¬r | yes s | no ¬t 
  = ⊥-elim (¬t (cong suc s))
... | no ¬r | no ¬s | yes t 
  = ⊥-elim (¬s (cong pred t))
... | no ¬r | no ¬s | no ¬t = {!!}
