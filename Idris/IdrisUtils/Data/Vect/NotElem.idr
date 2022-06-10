module IdrisUtils.Data.Vect.NotElem

import Data.Vect
import IdrisUtils.NotEq
import IdrisUtils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that some element is not in a vector.
data NotElem : (ord : TotalOrdering c) -> (x   : c) -> (xs  : Vect n c) -> Type where
  Here  : NotElem ord x [] 
  There : (notHere : NotEq {ord} x y) -> (notLater : NotElem ord x ys) -> NotElem ord x (y :: ys)

isNotElem : (ord : TotalOrdering c) -> (x : c) -> (xs : Vect n c) -> Dec (NotElem ord x xs)
isNotElem ord x [] = Yes Here
isNotElem ord x (y :: ys) with (decNotEq ord x y)
  | No here = No (\(There p q) => here p)
  | Yes notHere with (isNotElem ord x ys)
    | No there = No (\(There p q) => there q)
    | Yes notThere = Yes (There notHere notThere)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotElem_sound : (p : NotElem ord x xs) -> Not (Elem x xs)
lemma_NotElem_sound Here x = absurd x
lemma_NotElem_sound (There notHere notLater) Here = lemma_NotEq_irreflexive notHere
lemma_NotElem_sound (There notHere notLater) (There later) = lemma_NotElem_sound notLater later

lemma_NotElem_singleton : (ord : TotalOrdering c)
                       -> (x   : c)
                       -> (xs  : Vect n c)
                       -> (p   : NotElem ord x xs)
                       -> (q   : NotElem ord x xs)
                       -> p = q
lemma_NotElem_singleton ord x [] Here Here = Refl
lemma_NotElem_singleton ord x (y :: ys) (There p1 q1) (There p2 q2) =
  case (lemma_NotEq_singleton ord x y p1 p2, lemma_NotElem_singleton ord x ys q1 q2) of
    (Refl, Refl) => Refl
