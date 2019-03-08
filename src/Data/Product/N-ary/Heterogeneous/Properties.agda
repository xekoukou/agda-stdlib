------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Products
------------------------------------------------------------------------


module Data.Product.N-ary.Heterogeneous.Properties where

open import Data.Product.N-ary.Heterogeneous
open import Data.Nat
open import Data.Fin
import Level as L
open import Data.Product
open import Relation.Binary.PropositionalEquality


infix 4 _≅_

data _≅_ {ℓ1} {A : Set ℓ1} (x : A) : ∀ {ℓ2} → {B : Set ℓ2} → B → Set ℓ1 where
   refl : x ≅ x

------------------------------------------------------------------------
-- Conversion

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl



lemma1 : ∀ n {ls} → Product′ n (sucSets n ls) ≡ Sets n ls
lemma1 zero = refl
lemma1 (suc n) = cong (λ z → _ × z) (lemma1 n)

lemma2 : ∀ {n ls} → ∀ k → Levelₙ (sucs n ls) k ≡ L.suc (Levelₙ ls k)
lemma2 zero = refl
lemma2 {_} {l , ls} (suc k) = lemma2 {_} {ls} k



lemma5 : ∀ l1 l2 → l1 ≡ l2 → Set l1 ≅ Set l2
lemma5 l1 .l1 refl = refl

-- lemma3 : ∀ n {ls} → ∀ k → let q = subst (λ x → {!!}) (sym (lemma2 {n} {ls} k)) (Set (Levelₙ ls k))
--                           in Projₙ (sucSets n ls) k ≡ {!q!} -- Set (Levelₙ ls k)
-- lemma3 = {!!}

-- lemma4 : ∀ n {ls} k → (p : Product′ n (sucSets n ls)) → let p′ = subst _ (lemma1 n) p in projₙ′ n k p ≡ {!Projₙ ? k!}
-- lemma4 = {!!}
