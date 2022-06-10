module IdrisUtils.Data.Vect.Elem

import Data.Vect
import IdrisUtils.Ord
import IdrisUtils.NotEq
import IdrisUtils.Decidability

import IdrisUtils.Data.Vect.NotElem

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that some element is found in a vector.
|||
||| Under this definition the proof points at *all* occurrences of the given element.
||| An alternative that points at only the *first* ocurrence of the given element would be equally
||| valid.
|||
||| Stricter than Data.Vect.Elem.
||| Designed to have the property that there is only one way to construct a value of `Elem` for a 
||| given `x` and `xs` .
|||
||| This strictness is useful, e.g., when constructing contradictions for `decEq` implementations.
data Elem : (ord : TotalOrdering c) -> (x : c) -> (xs : Vect n c) -> Type where
  JustHere : (notThere : NotElem ord x ys) -> Elem ord x (x :: ys)
  JustThere : (notHere : NotEq {ord} x y) -> (there : Elem ord x ys) -> Elem ord x (y :: ys)
  HereAndThere : (there : Elem ord x ys) -> Elem ord x (x :: ys)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Uninhabited (Elem ord x []) where
  uninhabited JustHere impossible
  uninhabited JustThere impossible
  uninhabited HereAndThere impossible

isElem_thereAndNotThere : (np : Not (Elem ord x ys))
                       -> (nq : Not (NotElem ord x ys))
                       -> Not (Elem ord x (x :: ys))
isElem_thereAndNotThere np nq (JustHere r) = nq r
isElem_thereAndNotThere np nq (JustThere r1 r2) = np r2
isElem_thereAndNotThere np nq (HereAndThere r) = np r

isElem_neitherHereNorThere : (p : NotEq {ord} x y)
                          -> (contra : Not (Elem ord x ys))
                          -> Not (Elem ord x (y :: ys))
isElem_neitherHereNorThere p contra (JustHere q) = lemma_NotEq_sound p Refl
isElem_neitherHereNorThere p contra (JustThere q r) = contra r
isElem_neitherHereNorThere p contra (HereAndThere r) = contra r

isElem : NotEq.DecEq c => (x : c) -> (xs : Vect n c) -> Dec (Elem Ord.order x xs)
isElem x [] = No absurd
isElem x (y :: ys) with (decEq x y)
  isElem x (x :: ys) | Yes Refl with (isElem x ys)
    isElem x (x :: ys) | Yes Refl | Yes there = Yes (HereAndThere there)
    isElem x (x :: ys) | Yes Refl | No nthere with (isNotElem order x ys)
      isElem x (x :: ys) | Yes Refl | No nthere | Yes notThere =
        Yes (JustHere notThere)
      isElem x (x :: ys) | Yes Refl | No nthere | No there =
        No (isElem_thereAndNotThere nthere there)
  isElem x (y :: ys) | No neq with (isElem x ys)
    isElem x (y :: ys) | No neq | Yes there = Yes (JustThere neq there)
    isElem x (y :: ys) | No neq | No nthere = No (isElem_neitherHereNorThere neq nthere)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Elem_sound : (p : Elem ord x xs) -> Not (NotElem ord x xs)
lemma_Elem_sound (JustHere p) (There q r) = lemma_NotEq_irreflexive q
lemma_Elem_sound (JustThere p q) (There r s) = lemma_Elem_sound q s
lemma_Elem_sound (HereAndThere p) (There q r) = lemma_Elem_sound p r

lemma_Elem_singleton : (p, q : Elem ord x xs) -> p = q
lemma_Elem_singleton {ord} {x} {xs = x :: ys} (JustHere p) (JustHere q)
  with (lemma_NotElem_singleton ord x ys p q)
    lemma_Elem_singleton {ord} {x} {xs = x :: ys} (JustHere p) (JustHere p) | Refl = Refl
lemma_Elem_singleton (JustHere p) (JustThere q r) with (lemma_NotEq_irreflexive q)
  lemma_Elem_singleton (JustHere p) (JustThere q r) | _ impossible
lemma_Elem_singleton (JustHere p) (HereAndThere q) with (lemma_Elem_sound q p)
  lemma_Elem_singleton (JustHere p) (HereAndThere q) | _ impossible
lemma_Elem_singleton (JustThere p q) (JustHere r) with (lemma_NotEq_irreflexive p)
  lemma_Elem_singleton (JustThere p q) (JustHere r) | _ impossible
lemma_Elem_singleton {ord} {x} {xs = y :: ys} (JustThere p q) (JustThere r s)
  with (lemma_NotEq_singleton ord x y p r, lemma_Elem_singleton q s)
    lemma_Elem_singleton (JustThere p q) (JustThere p q) | (Refl, Refl) = Refl
lemma_Elem_singleton (JustThere p q) (HereAndThere r) with (lemma_NotEq_irreflexive p)
  lemma_Elem_singleton (JustThere p q) (HereAndThere r) | _ impossible
lemma_Elem_singleton (HereAndThere p) (JustHere q) with (lemma_Elem_sound p q)
  lemma_Elem_singleton (HereAndThere p) (JustHere q) | _ impossible
lemma_Elem_singleton (HereAndThere p) (JustThere q r) with (lemma_NotEq_irreflexive q)
  lemma_Elem_singleton (HereAndThere p) (JustThere q r) | _ impossible
lemma_Elem_singleton (HereAndThere p) (HereAndThere q) with (lemma_Elem_singleton p q)
  lemma_Elem_singleton (HereAndThere p) (HereAndThere p) | Refl = Refl

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotElem_sound : (p : NotElem ord x xs) -> Not (Elem ord x xs)
lemma_NotElem_sound (There p q) (JustHere r) = lemma_NotEq_irreflexive p
lemma_NotElem_sound (There p q) (JustThere r s) = lemma_Elem_sound s q
lemma_NotElem_sound (There p q) (HereAndThere r) = lemma_NotEq_irreflexive p

PropElem : NotEq.DecEq c => (x : c) -> (xs : Vect n c) -> Prop
PropElem x xs =
  MkProp (Elem order x xs) (NotElem order x xs)
         (isElem x xs) (isNotElem order x xs)
         lemma_Elem_sound lemma_NotElem_sound

interface NotEq.DecEq c => DecElem c where
  decElem : (x : c) -> (xs : Vect n c) -> Dec (PropElem x xs)

DecidableElem : DecElem c => (x : c) -> (xs : Vect n c) -> Decidable (PropElem x xs)
DecidableElem x xs = IsDecidable (decElem x xs)
