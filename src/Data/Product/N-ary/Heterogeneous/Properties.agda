------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Products
------------------------------------------------------------------------


module Data.Product.N-ary.Heterogeneous.Properties where

open import Data.Product.N-ary.Heterogeneous
open import Data.Nat 
open import Data.Fin hiding (pred)
import Level as L
open import Data.Product
open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H


-- Product ≅ Sets

lemma1 : ∀ n {ls} → Product′ n (sucSets n ls) ≡ Sets n ls
lemma1 zero = refl
lemma1 (suc n) = cong (λ z → _ × z) (lemma1 n)


-- Proj ≅ proj
mutual

-- generalize this abstraction
  lemma4-abs : ∀ n {l ls ss} → {w : Set _} → w ≡ Sets n ls → (p : Set l × w)
           → ss H.≅ p
           → proj₁ ss H.≅ proj₁ p
  lemma4-abs n refl p H.refl = H.refl

  lemma4-abs2 : ∀{n l ls s p ps} → ∀{w} → (eq : w ≡ Product′ n (sucSets n ls)) → {ss : w}
                → (s , ss) H.≅ (p , ps) → ss H.≅ ps
  lemma4-abs2 {s = s} {.s} refl H.refl = H.refl

  lemma4 : ∀ n {ls ss} k → (p : Product′ n (sucSets n ls))
           → ss H.≅ p
           → Projₙ {n} {ls} ss k H.≅ projₙ′ n k p
  lemma4 (suc n) {l , ls} zero p eq = lemma4-abs n {l} {ls} (lemma1 n) p eq
  lemma4 (suc n) {l , ls} {s , ss} (suc k) (p , ps) eq = lemma4 n {ls} {ss} k ps (lemma4-abs2 {n} {l} {ls} {s} {p} {ps} {_} (sym (lemma1 n {ls})) {ss} eq)



lemma6 : ∀{n ls } k → sucs (pred n) (Levelₙ⁻ ls k) ≡ Levelₙ⁻ (sucs n ls) k
lemma6 zero = refl
lemma6 {suc zero} {ls} (suc ())
lemma6 {suc (suc n)} {l , ls} (suc k) = cong (λ z → L.suc l , z) (lemma6 k)

-- Remove ≅ remove
mutual
-- generalize this abstraction
  lemma5-abs1 : ∀{n l ls s p ps} → ∀{w} → (eq : w ≡ Product′ n (sucSets n ls)) → {ss : w}
                → (s , ss) H.≅ (p , ps) → ss H.≅ ps
  lemma5-abs1 refl H.refl = H.refl

  lemma5-abs2 : ∀{n lo l ls so s ss po p ps} → ∀ k {L} {W : Set L} {w : W}
                → Removeₙ {suc n} {l , ls} (s , ss) k H.≅ w → so H.≅ po
                → (so , Removeₙ {suc n} {l , ls} (s , ss) k) H.≅ (po , w)
  lemma5-abs2 {n} {lo} {l} {ls} {so} {s} {ss} {.so} {p} {ps} zero {_} {_} {.ss} H.refl H.refl = H.refl
  lemma5-abs2 {n} {lo} {l} {ls} {so} {s} {ss} {.so} {p} {ps} (suc k) H.refl H.refl = H.refl
    

-- Product′ n (Removeₙ (Set l , sucSets n ls) k) == Sets n (Levelₙ⁻ (l , ls) k)
  
  lemma5 : ∀ n {ls ss} k → (p : Product′ n (sucSets n ls))
           → ss H.≅ p
           → Removeₙ {n} {ls} ss k H.≅ removeₙ′ n k p
  lemma5 (suc n) {l , ls} {s , ss} zero (p , ps) eq = lemma5-abs1 {n} {l} {ls} {s} {p} {ps} {_} ((sym (lemma1 n {ls}))) eq
  lemma5 (suc zero) (suc ()) p eq
  lemma5 (suc (suc n)) {lo , l , ls} {so , s , ss} (suc k) (po , p , ps) eq
    = lemma5-abs2 {n} {lo} {l} {ls} {so} {s} {ss} {po} {p} {ps} k
                  (lemma5 (suc n) k (p , ps) ((lemma5-abs1 {suc n} {lo} {l , ls} {so} {po} {p , ps} (sym (lemma1 (suc n) {l , ls})) eq) )) (lemma4-abs ((suc n)) (lemma1 (suc n) {l , ls}) (po , p , ps) eq)
