module IdrisUtils.Data.Vect.IsSet

import IdrisUtils.Ord

import Data.Vect
import IdrisUtils.Data.Vect.NotElem

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that a given vector has no duplicate (totally ordered) elements.
data IsSet : (ord : TotalOrdering c) -> (xs : Vect n c) -> Type where
  Nil  : IsSet ord []
  (::) : (here : NotElem ord x xs) -> (there : IsSet ord xs) -> IsSet ord (x :: xs)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

decIsSet : (ord : TotalOrdering c) -> (xs : Vect n c) -> Dec (IsSet ord xs)
decIsSet ord [] = Yes Nil
decIsSet ord (x :: xs) with (isNotElem ord x xs)
  | No nhere = No (\(p :: q) => nhere p)
  | Yes here with (decIsSet ord xs)
    | No nthere = No (\(_ :: there) => nthere there)
    | Yes there = Yes (here :: there)

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Equality.DecEq (IsSet ord xs) where
  decEq Nil Nil = Yes Refl
  decEq {ord} {xs = (x :: xs)} (neq_p :: p) (neq_q :: q) =
    case decEq p q of
      No neq_tlset => No (\Refl => neq_tlset Refl)
      Yes Refl =>
        case lemma_NotElem_singleton ord x xs neq_p neq_q of
          Refl => Yes Refl

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_IsSet_singleton : (p,q : IsSet ord xs) -> p = q
lemma_IsSet_singleton Nil Nil = Refl
lemma_IsSet_singleton {ord} {xs = x :: xs} (p :: ps) (q :: qs) =
  case (lemma_NotElem_singleton ord x xs p q, lemma_IsSet_singleton ps qs) of
    (Refl, Refl) => Refl
