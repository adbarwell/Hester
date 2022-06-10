module IdrisUtils.NotEq

import public IdrisUtils.Ord
import IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that two values of the same type are not (propositionally) equal.
|||
||| Takes advantage of the fact that the given type is totally ordered to avoid equality proofs;
||| specifically, x ≠ y iff (x > y) \/ (x < y).
data NotEq : {ord : TotalOrdering c}
          -> (x   : c)
          -> (y   : c)
          -> Type where
  IsLT : (lt : proj_LT ord x y) -> NotEq {ord} x y
  IsGT : (gt : proj_LT ord y x) -> NotEq {ord} x y

decNotEq_xEQy : (nlt : Not (proj_LT ord x y))
             -> (ngt : Not (proj_LT ord y x))
             -> Not (NotEq {ord} x y)
decNotEq_xEQy nlt ngt (IsLT lt) = nlt lt
decNotEq_xEQy nlt ngt (IsGT gt) = ngt gt

decNotEq : (ord : TotalOrdering c) -> (x,y : c) -> Dec (NotEq {ord = ord} x y)
decNotEq ord x y with (proj_isLT ord x y)
  | Yes lt = Yes (IsLT lt)
  | No nlt with (proj_isLT ord y x)
    | Yes gt = Yes (IsGT gt)
    | No ngt = No (decNotEq_xEQy nlt ngt)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotEq_sound : (p : NotEq x y) -> Not (x = y)
lemma_NotEq_sound {x} (IsLT {ord} lt) Refl = proj_irrefl ord x lt
lemma_NotEq_sound {x} (IsGT {ord} gt) Refl = proj_irrefl ord x gt

lemma_NotEq_singleton : (ord : TotalOrdering c) -> (x : c) -> (y : c)
                     -> (p : NotEq {ord = ord} x y) -> (q : NotEq {ord = ord} x y) -> p = q
lemma_NotEq_singleton ord x y (IsLT p) (IsLT q) with (proj_sing ord x y p q)
  lemma_NotEq_singleton ord x y (IsLT p) (IsLT p) | Refl = Refl
lemma_NotEq_singleton ord x y (IsLT p) (IsGT q) with (proj_antisym ord x y p q)
  lemma_NotEq_singleton ord x y (IsLT p) (IsGT q) | _ impossible
lemma_NotEq_singleton ord x y (IsGT p) (IsGT q) with (proj_sing ord y x p q)
  lemma_NotEq_singleton ord x y (IsGT p) (IsGT p) | Refl = Refl
lemma_NotEq_singleton ord x y (IsGT p) (IsLT q) with (proj_antisym ord y x p q)
  lemma_NotEq_singleton ord x y (IsGT p) (IsLT q) | _ impossible

lemma_NotEq_irreflexive : (p : NotEq x x) -> Void
lemma_NotEq_irreflexive {x} (IsLT {ord} lt) = proj_irrefl ord x lt
lemma_NotEq_irreflexive {x} (IsGT {ord} gt) = proj_irrefl ord x gt

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_PropEq_sound : (x = y) -> Not (NotEq x y)
lemma_PropEq_sound {x} Refl (IsLT {ord} p) = proj_irrefl ord x p
lemma_PropEq_sound {x} Refl (IsGT {ord} p) = proj_irrefl ord x p

PropDecEq : (ord : TotalOrdering c) -> (x, y : c) -> Prop
PropDecEq ord x y =
  MkProp (x = y) (NotEq {ord = ord} x y)
         (proj_decEq ord x y) (decNotEq ord x y)
         lemma_PropEq_sound lemma_NotEq_sound

interface TotalOrder c => DecEq c where
  decEq : (x, y : c) -> Dec (PropDecEq Ord.order x y)

DecidableEq : NotEq.DecEq c => (x, y : c) -> Decidable (PropDecEq Ord.order x y)
DecidableEq x y = IsDecidable (decEq x y)
