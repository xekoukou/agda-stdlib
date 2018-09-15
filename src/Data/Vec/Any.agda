------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.Vec.Any {a} {A : Set a} where

open import Data.Empty
open import Data.Fin
open import Data.Nat using (zero; suc)
open import Data.Vec as Vec using (Vec; []; [_]; _∷_)
open import Data.Product as Prod using (∃; _,_)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary

------------------------------------------------------------------------
-- Any P xs means that at least one element in xs satisfies P.

data Any {p} (P : Pred A p) : ∀ {n} → Vec A n → Set p where
  here  : ∀ {n x xs} (px  : P x)      → Any P {suc n} (x ∷ xs)
  there : ∀ {n x xs} (pxs : Any P {n} xs) → Any P {suc n} (x ∷ xs)

------------------------------------------------------------------------
-- Operations on Any

module _ {p} {P : Pred A p} where

-- If the head does not satisfy the predicate, then the tail will.
  tail : ∀ {n} {xs : Vec A (suc n)} →
         ¬ P (Vec.head xs) → Any P xs → Any P (Vec.tail xs)
  tail {xs = x ∷ xs} ¬px (here px)   = ⊥-elim (¬px px)
  tail {xs = x ∷ xs} ¬px (there pxs) = pxs

  index : ∀ {n xs} → Any P {n} xs → Fin n
  index (here  px)  = zero
  index (there pxs) = suc (index pxs)

-- If any element satisfies P, then P is satisfied.
  satisfied : ∀ {n xs} → Any P {n} xs → ∃ P
  satisfied (here px)   = _ , px
  satisfied (there pxs) = satisfied pxs

map : ∀ {p q} {P : A → Set p} {Q : A → Set q} →
      P ⊆ Q → ∀ {n} → Any P {n} ⊆ Any Q {n}
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)


------------------------------------------------------------------------
-- Properties of predicates preserved by Any

module _ {p} {P : Pred A p} where

  any : Decidable P → ∀ {n} → Decidable (Any P {n})
  any P? []       = no λ()
  any P? (x ∷ xs) with P? x
  ... | yes px = yes (here px)
  ... | no ¬px = Dec.map′ there (tail ¬px) (any P? xs)

  satisfiable : Satisfiable P → ∀ {n} → Satisfiable (Any P {suc n})
  satisfiable (x , p) {zero}  = x ∷ [] , here p
  satisfiable (x , p) {suc n} = Prod.map (x ∷_) there (satisfiable (x , p))
