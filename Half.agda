module Half where

-- http://staff.aist.go.jp/reynald.affeldt/tpp2011/garrigue_candy.v

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

open import MinMaxLe

half : ℕ -> ℕ
half zero = zero
half (suc zero) = suc zero
half (suc (suc n)) = suc (half n)

≤-half-refl : ∀ n -> half n ≤ half n
≤-half-refl zero = z≤n
≤-half-refl (suc zero) = s≤s z≤n
≤-half-refl (suc (suc n)) 
  = ≤-suc-suc (≤-half-refl n)

≤-suc-≡ : ∀ m n -> m ≡ n -> suc m ≤ suc n
≤-suc-≡ zero zero p = ≤-suc-suc z≤n
≤-suc-≡ zero (suc n) ()
≤-suc-≡ (suc m) zero ()
≤-suc-≡ (suc m) (suc n) p 
  = ≤-suc-suc (≤-suc-≡ m n (cong pred p))

≤-half-≡ : ∀ m n -> m ≡ n -> half m ≤ half n
≤-half-≡ zero n p = z≤n
≤-half-≡ (suc zero) zero ()
≤-half-≡ (suc zero) (suc zero) p = s≤s z≤n
≤-half-≡ (suc zero) (suc (suc n)) ()
≤-half-≡ (suc (suc m)) zero ()
≤-half-≡ (suc (suc m)) (suc zero) ()
≤-half-≡ (suc (suc m)) (suc (suc n)) p 
  = ≤-suc-suc 
     (≤-half-≡ m n (cong (λ x -> pred (pred x)) p))

-- lemma: half-le
half-le : ∀ n -> half n ≤ n
half-le zero = z≤n
half-le (suc zero) = s≤s z≤n
half-le (suc (suc n)) = begin
  half (suc (suc n)) ≤⟨ s≤s (≤-half-refl n) ⟩
  suc (half n) ≤⟨ ≤-suc-suc (half-le n) ⟩
  suc n ≤⟨ s≤s (≤-suc n) ⟩
  suc (suc n)
  ∎
  where open ≤-Reasoning

half-exact-le : ∀ m n -> m ≤ n -> half m ≤ n
half-exact-le zero n p = z≤n
half-exact-le (suc zero) n p = p
half-exact-le (suc (suc m)) zero ()
half-exact-le (suc (suc m)) (suc n) p = begin
  suc (half m) 
    ≤⟨ ≤-suc-suc (half-exact-le m (suc m) (≤-suc m)) ⟩
  suc (suc m) ≤⟨ p ⟩
  suc n  
  ∎
  where open ≤-Reasoning

-- lemma: half-double
half-double : ∀ n -> half (n + n) ≡ n
half-double zero = refl
half-double (suc zero) = refl
half-double (suc (suc n)) = begin
  half (suc (suc n) + suc (suc n)) ≡⟨ refl ⟩
  suc (half (n + suc (suc n))) 
    ≡⟨ cong (λ m → suc (half m)) (lemma1 n) ⟩
  suc (half (suc (suc (n + n)))) ≡⟨ cong suc refl ⟩
  suc (suc (half (n + n))) 
    ≡⟨ cong (λ m → suc (suc m)) (half-double n) ⟩
  suc (suc n)
  ∎
  where open ≡-Reasoning
        lemma1 : ∀ n -> (n + suc (suc n)) ≡ suc (suc (n + n))
        lemma1 zero = refl
        lemma1 (suc n) = begin
          suc n + (suc (suc (suc n))) 
            ≡⟨ +-comm (suc n) (suc (suc (suc n))) ⟩
          suc (suc (suc n)) + suc n ≡⟨ refl ⟩ 
          suc (suc (suc n + suc n))
          ∎

-- lemma: half-grows
half-grows : ∀ m n -> m ≤ n -> half m ≤ half n
half-grows zero n p = z≤n
half-grows (suc zero) zero p = p
half-grows (suc zero) (suc zero) p = p
half-grows (suc zero) (suc (suc n)) p = s≤s z≤n
half-grows (suc (suc m)) zero ()
half-grows (suc (suc m)) (suc zero) p with begin
  suc m ≤⟨ ≤-pred p ⟩
  zero
  ∎
  where open ≤-Reasoning
...| () 
half-grows (suc (suc m)) (suc (suc n)) p 
  = begin
      suc (half m) 
        ≤⟨ ≤-suc-suc (half-grows m n (≤-pred (≤-pred p))) ⟩
      suc (half n) 
    ∎
  where open ≤-Reasoning

-- lemma: half-max
half-max : ∀ m n -> half (m + n) ≤ m ⊔ n
half-max zero n = half-le n
half-max (suc zero) zero = s≤s z≤n
half-max (suc zero) (suc zero) 
  = half-max zero (suc zero)
half-max (suc zero) (suc (suc n)) 
  = ≤-suc-suc (half-le (suc n))
half-max (suc (suc m)) zero = begin
  suc (half (m + zero)) ≤⟨ s≤s (lemma1 m) ⟩
  suc (half m) ≤⟨ s≤s (half-le m) ⟩
  suc m ≤⟨ s≤s (≤-suc m) ⟩
  suc (suc m)
  ∎
  where open ≤-Reasoning
        lemma1 : ∀ m -> half (m + zero) ≤ half m
        lemma1 zero = z≤n
        lemma1 (suc zero) = s≤s z≤n
        lemma1 (suc (suc m)) = s≤s (lemma1 m)
half-max (suc (suc m)) (suc zero) 
  = s≤s (lemma1 m)
  where open ≤-Reasoning
        lemma1 : ∀ m -> half (m + (suc zero)) ≤ suc m
        lemma1 m = begin
          half (m + (suc zero)) 
            ≤⟨ ≤-half-≡ (m + suc zero) 
                          (suc m) (+-comm m (suc zero)) ⟩
          half (suc m) ≤⟨ half-le (suc m) ⟩
          suc m
          ∎
half-max (suc (suc m)) (suc (suc n)) = begin
  suc (half (m + suc (suc n))) 
    ≤⟨ ≤-suc-suc (≤-half-≡ (m + suc (suc n)) 
                     (suc (suc (n + m)))
                     (+-comm m (suc (suc n)))) ⟩
  suc (half (suc (suc n) + m)) 
    ≤⟨ s≤s (≤-suc-suc (≤-half-≡ (n + m) (n + m) refl)) ⟩
  suc (half (suc (suc (n + m)))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc 
        (≤-half-≡ (n + m) (m + n) (+-comm n m))) ⟩
  suc (half (suc (suc (m + n)))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc (half-max m n)) ⟩
  suc (suc (m ⊔ n))
  ∎
  where open ≤-Reasoning

-- lemma: half-min
half-min : ∀ m n -> m ⊓ n ≤ half (m + n)
half-min zero n = z≤n
half-min (suc zero) zero = z≤n
half-min (suc zero) (suc zero) = s≤s z≤n
half-min (suc zero) (suc (suc n)) = s≤s z≤n
half-min (suc (suc m)) zero = z≤n
half-min (suc (suc m)) (suc zero) = s≤s z≤n
half-min (suc (suc m)) (suc (suc n)) = begin
  suc (suc (m ⊓ n)) 
    ≤⟨ ≤-suc-suc (≤-suc-suc (half-min m n)) ⟩
  suc (suc (half (m + n))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc 
          (≤-half-≡ (m + n) (n + m) (+-comm m n))) ⟩
  suc (suc (half (n + m)))
    ≤⟨ ≤-suc-suc (≤-suc-suc 
          (≤-half-≡ (n + m) (n + m) refl)) ⟩
  suc (half (suc (suc (n + m))))
    ≤⟨ ≤-suc-suc (≤-suc-suc 
        (≤-half-≡ (n + m) (n + m) refl)) ⟩
  suc (half (suc (suc n) + m))   
    ≤⟨ ≤-suc-suc (≤-half-≡ 
          (suc (suc (n + m))) 
          (m + suc (suc n)) 
          (+-comm (suc (suc n)) m)) ⟩
  suc (half (m + suc (suc n)))
  ∎
  where open ≤-Reasoning

-- lemma: half-neq
half-neq : ∀ m n -> m < n -> m < half (m + n)
half-neq zero zero ()
half-neq zero (suc zero) p = p
half-neq zero (suc (suc n)) p = s≤s z≤n
half-neq (suc zero) zero ()
half-neq (suc zero) (suc zero) p with ≤-pred p
... | ()
half-neq (suc zero) (suc (suc n)) p = begin
  suc (suc zero) 
    ≤⟨ ≤-suc-suc (half-neq zero (suc n) (s≤s z≤n)) ⟩
  suc (half (suc zero + n)) 
    ≤⟨ ≤-half-≡ (suc (suc (suc n))) (suc (suc (suc n))) refl ⟩
  suc (half (suc n))
  ∎
  where open ≤-Reasoning
half-neq (suc (suc m)) zero ()
half-neq (suc (suc m)) (suc zero) p with ≤-pred p
... | ()
half-neq (suc (suc m)) (suc (suc n)) p = begin
  suc (suc (suc m)) 
    ≤⟨ ≤-suc-suc (≤-suc-suc (half-neq m n (≤-pred (≤-pred p)))) ⟩
  suc (suc (half (m + n))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc 
        (≤-half-≡ (m + n) (n + m) (+-comm m n))) ⟩
  suc (suc (half (n + m))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc 
        (≤-half-≡ (n + m) (n + m) refl)) ⟩
  suc (half (suc (suc (n + m)))) 
    ≤⟨ ≤-suc-suc (≤-suc-suc 
        (≤-half-≡ (n + m) (n + m) refl)) ⟩
  suc (half (suc (suc n) + m)) 
    ≤⟨ ≤-suc-suc (≤-half-≡ (suc (suc (n + m)))
          (m + suc (suc n)) (+-comm (suc (suc n)) m)) ⟩
  suc (half (m + suc (suc n)))
  ∎
  where open ≤-Reasoning

-- use half-neq : ∀ m n -> m < n -> m < half (m + n)
-- lemma: half-loop
half-loop : ∀ m n -> m ≤ n -> half (m + n) ≤ m -> n ≡ m
half-loop zero zero p q = refl
half-loop zero (suc zero) p ()
half-loop zero (suc (suc n)) p q with begin
  suc (half n) ≤⟨ q ⟩
  zero
  ∎
  where open ≤-Reasoning
... | ()
half-loop (suc zero) zero () q 
half-loop (suc zero) (suc zero) p q = refl
half-loop (suc zero) (suc (suc n)) p q with begin
  suc zero ≤⟨ half-neq zero (suc n) (s≤s z≤n) ⟩
  half (suc zero + n) 
    ≤⟨ ≤-half-≡ (suc n) (suc n) refl ⟩
  half (suc n) ≤⟨ ≤-pred q ⟩
  zero
  ∎
  where open ≤-Reasoning
... | ()
half-loop (suc (suc m)) zero () q 
half-loop (suc (suc m)) (suc zero) p q with ≤-pred p
... | ()
half-loop (suc (suc m)) (suc (suc n)) p q 
  = cong (λ x -> suc (suc x)) 
    (half-loop m n (≤-pred (≤-pred p)) lemma1)
  where open ≤-Reasoning
        lemma2 : suc (suc (half (m + n))) ≤ suc (suc m)
        lemma2 = begin
          suc (suc (half (m + n))) 
            ≤⟨ ≤-suc-suc (≤-suc-suc 
                (≤-half-≡ (m + n) (n + m) (+-comm m n))) ⟩
          suc (suc (half (n + m))) 
            ≤⟨ ≤-suc-suc (≤-suc-suc 
                (≤-half-≡ (n + m) (n + m) refl)) ⟩
          suc (half (suc (suc (n + m)))) 
            ≤⟨ ≤-suc-suc (≤-half-≡ (suc (suc (n + m))) 
                (suc (suc (n + m))) refl) ⟩
          suc (half ((suc (suc n)) + m)) 
            ≤⟨ ≤-suc-suc (≤-half-≡ (suc (suc (n + m))) 
               (m + suc (suc n)) (+-comm (suc (suc n)) m)) ⟩
          suc (half (m + suc (suc n))) ≤⟨ q ⟩
          suc (suc m)
          ∎
        lemma1 : half (m + n) ≤ m
        lemma1 = begin
          half (m + n) ≤⟨ ≤-pred (≤-pred lemma2) ⟩
          m
          ∎
