module test-001 where

open import Level using (0ℓ)
open import Data.Nat
import Data.Fin as Fin
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.Maybe
open import Data.Vec as Vec
open import Codata.Colist as Colist
open import Codata.Stream as Stream
import Codata.Musical.Colist as MColist
open import Codata.Musical.Cofin as MCofin
open import Codata.Musical.Covec as Covec
import Codata.Musical.Stream as MStream
open import Function
open import Relation.Binary.PropositionalEquality
open import Foreign.Haskell
open import Data.Product
open import Category.Monad
open import Data.List.Categorical
open import Data.BoundedVec as BVec
open import Agda.Builtin.Int
open import Data.Integer using (-[1+_])
open import Data.Rational
open import Data.Integer.Properties using (+-injective)

open RawMonad {0ℓ} monad

test : (A : Set) → MStream.Stream A → ℕ → List A
test A xs n = List.[_] ∘′ proj₂ =<<_
  $ BVec.toList
  $ Colist.take 10
  $ Colist.map (λ where (unit , a) → (-[1+ 0 ] ÷ 1 , a))
  $ Colist.map ((A → Pair Unit A) ∋ unit ,_)
  $ Colist.fromMusical
  $ MColist.fromList
  $ List⁺.toList
  $ List⁺.fromVec {n = n}
  $ Vec.replicate ∘′ Covec.lookup zero
  $ Covec.fromVec
  $ subst (Vec A) (+-injective $ cong pos $ +-comm n 10)
  $ Stream.take (n + 10)
  $ Stream.fromMusical xs
