module MinMaxLe where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

≤-suc : ∀ n -> n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

≤-refl : ∀ n -> n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-suc-suc : ∀ {m n} -> m ≤ n -> suc m ≤ suc n
≤-suc-suc p = s≤s p

≤-elim-min-left : ∀ m n -> m ⊓ n ≤ n
≤-elim-min-left zero n = z≤n
≤-elim-min-left (suc m) zero = z≤n
≤-elim-min-left (suc m) (suc n) = begin
  suc (m ⊓ n) ≤⟨ s≤s (≤-refl (m ⊓ n)) ⟩ 
  suc m ⊓ suc n ≤⟨ s≤s (≤-elim-min-left m n) ⟩
  suc n
  ∎
  where open ≤-Reasoning

≤-add-max-right : ∀ m n -> m ≤ m ⊔ n
≤-add-max-right zero n = z≤n
≤-add-max-right (suc m) zero = ≤-refl (suc m)
≤-add-max-right (suc m) (suc n) = begin
  suc m ≤⟨ s≤s (≤-add-max-right m n) ⟩
  suc m ⊔ suc n ≤⟨ s≤s (≤-refl (m ⊔ n)) ⟩
  suc (m ⊔ n)
  ∎
  where open ≤-Reasoning

≤-add-max-left : ∀ m n -> m ≤ n ⊔ m
≤-add-max-left zero n = z≤n
≤-add-max-left (suc m) zero = ≤-refl (suc m)
≤-add-max-left (suc m) (suc n) = begin
  suc m ≤⟨ s≤s (≤-add-max-left m n) ⟩
  suc (n ⊔ m)
  ∎
  where open ≤-Reasoning

≤-max-comm : ∀ m n -> m ⊔ n ≤ n ⊔ m
≤-max-comm zero zero = z≤n
≤-max-comm zero (suc n) = s≤s (≤-refl n)
≤-max-comm (suc m) zero = ≤-refl (suc m)
≤-max-comm (suc m) (suc n) = begin
  suc (m ⊔ n) ≤⟨ ≤-suc-suc (≤-max-comm m n) ⟩
  suc (n ⊔ m)
  ∎
  where open ≤-Reasoning

≤-min-comm : ∀ m n -> m ⊓ n ≤ n ⊓ m
≤-min-comm zero zero = z≤n
≤-min-comm zero (suc n) = z≤n
≤-min-comm (suc m) zero = z≤n
≤-min-comm (suc m) (suc n) = begin
  suc (m ⊓ n) ≤⟨ ≤-suc-suc (≤-min-comm m n) ⟩
  suc (n ⊓ m)
  ∎
  where open ≤-Reasoning

≤-refl-≡ : ∀ m n -> m ≡ n -> m ≤ n
≤-refl-≡ .n n refl = ≤-refl n

≤-plus-act-right : ∀ l m n -> m ≤ n -> l + m ≤ l + n
≤-plus-act-right zero m n p = p
≤-plus-act-right (suc l) m n p 
  = ≤-suc-suc (≤-plus-act-right l m n p)

≤-max-act-left : ∀ x y z -> x ≤ y -> x ⊔ z ≤ y ⊔ z
≤-max-act-left zero zero z p = ≤-refl z
≤-max-act-left zero (suc n) z p = ≤-add-max-left z (suc n)
≤-max-act-left (suc m) zero z ()
≤-max-act-left (suc m) (suc n) zero p = p
≤-max-act-left (suc m) (suc n) (suc z) p = begin
  suc (m ⊔ z) ≤⟨ s≤s (≤-refl (m ⊔ z)) ⟩
  suc m ⊔ suc z ≤⟨ ≤-suc-suc (≤-max-act-left m n z (≤-pred p))  ⟩
  suc n ⊔ suc z ≤⟨ s≤s (≤-refl (n ⊔ z)) ⟩ 
  suc (n ⊔ z)
  ∎
  where open ≤-Reasoning

≤-max-act-right : ∀ x y z -> y ≤ z -> x ⊔ y ≤ x ⊔ z
≤-max-act-right zero y z p = p
≤-max-act-right (suc x) zero z p 
  = ≤-add-max-right (suc x) z
≤-max-act-right (suc x) (suc m) zero ()
≤-max-act-right (suc x) (suc m) (suc n) p = begin
  suc (x ⊔ m) ≤⟨ s≤s (≤-refl (x ⊔ m)) ⟩
  suc x ⊔ suc m ≤⟨ ≤-suc-suc (≤-max-act-right x m n (≤-pred p)) ⟩
  suc x ⊔ suc n ≤⟨ s≤s (≤-refl (x ⊔ n)) ⟩
  suc (x ⊔ n)
  ∎
  where open ≤-Reasoning

≡-plus-zero-right : ∀ x -> x + zero ≡ x
≡-plus-zero-right 
  = proj₂ (CommutativeSemiring.+-identity commutativeSemiring)
  where open import Algebra
        open import Data.Nat.Properties
        open import Data.Product

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm = CommutativeSemiring.+-comm commutativeSemiring
  where open import Algebra

≤-plus-comm-left : ∀ x y z -> x + y ≤ z -> y + x ≤ z
≤-plus-comm-left zero zero z p = p
≤-plus-comm-left zero (suc n) zero ()
≤-plus-comm-left zero (suc n) (suc z) p = begin
  suc (n + zero) 
    ≤⟨ ≤-refl-≡ (suc (n + zero)) (suc n) 
                  (cong suc (≡-plus-zero-right n)) ⟩
  suc n ≤⟨ p ⟩
  suc z  
  ∎
  where open ≤-Reasoning
≤-plus-comm-left (suc n) zero z p = begin
  suc n ≤⟨ ≤-refl-≡ (suc n) (suc (n + zero)) 
             (cong suc (+-comm zero n)) ⟩
  suc (n + zero) ≤⟨ p ⟩
  z
  ∎
  where open ≤-Reasoning
≤-plus-comm-left (suc m) (suc n) zero ()
≤-plus-comm-left (suc m) (suc n) (suc z) p = begin
  suc (n + suc m) 
    ≤⟨ ≤-suc-suc (≤-plus-comm-left (suc m) n (suc (m + n)) (≤-refl (suc (m + n)))) ⟩
  suc (suc m + n) 
    ≤⟨ ≤-suc-suc (≤-refl-≡ (suc (m + n)) (m + suc n) (lemma1 m n)) ⟩
  suc (m + suc n) ≤⟨ p ⟩
  suc z
  ∎
  where open ≤-Reasoning
        lemma1 : ∀ x y -> suc (x + y) ≡ x + suc y
        lemma1 zero y = refl
        lemma1 (suc x) y = cong suc (lemma1 x y)

≤-max-assoc-left : ∀ x y z -> (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
≤-max-assoc-left zero y z = ≤-refl (y ⊔ z)
≤-max-assoc-left (suc m) zero z = ≤-refl (suc m ⊔ z)
≤-max-assoc-left (suc m) (suc n) zero = ≤-refl (suc (m ⊔ n))
≤-max-assoc-left (suc m) (suc n) (suc z) = begin
  suc (m ⊔ n ⊔ z) ≤⟨ ≤-suc-suc (≤-max-assoc-left m n z) ⟩
  suc (m ⊔ (n ⊔ z))
  ∎
  where open ≤-Reasoning

≤-max-assoc-right : ∀ x y z -> x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
≤-max-assoc-right zero y z = ≤-refl (y ⊔ z)
≤-max-assoc-right (suc m) zero z = ≤-refl (suc m ⊔ z)
≤-max-assoc-right (suc m) (suc n) zero = ≤-refl (suc (m ⊔ n))
≤-max-assoc-right (suc m) (suc n) (suc z) = begin
  suc (m ⊔ (n ⊔ z)) ≤⟨ ≤-suc-suc (≤-max-assoc-right m n z) ⟩
  suc (m ⊔ n ⊔ z)
  ∎
  where open ≤-Reasoning
