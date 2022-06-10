module Hs98.HsNameTy

import IdrisUtils.Utils

import public Hs98.HsNameTy.Name

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Assume a single module.
|||
||| Assume that symbols have been converted to a standard prefix name; e.g. `:` to `Cons`,
||| `[]` to `Nil`, `+` to `plus`. Having symbols doesn't really add anything interesting to our
||| representation, I think.
data HsNameTy : (k : HsNameKind) -> Type where
  HsIdentVar : (lv : Nat) -> (id : Nat) -> (na : Name Variable) -> HsNameTy Variable
  HsIdentCtr : (id : Nat) -> (na : Name Constructor) -> HsNameTy Constructor

---------------------------------------------------------------------------------------------------
-- [Relations] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HsIdentVarLv : (lv : Nat) -> (na : HsNameTy Variable) -> Type where
  MkHsIdentVarLv : HsIdentVarLv lv (HsIdentVar lv _ _)

decHsIdentVarLv : (lv : Nat) -> (var : HsNameTy Variable) -> Dec (HsIdentVarLv lv var)
decHsIdentVarLv lv (HsIdentVar x _ _) with (Equality.decEq x lv)
  decHsIdentVarLv lv (HsIdentVar x _ _)  | No  neq  = No (\MkHsIdentVarLv => neq Refl)
  decHsIdentVarLv lv (HsIdentVar lv _ _) | Yes Refl = Yes MkHsIdentVarLv

lemma_HsIdentVarLv_singleton : (y : HsNameTy Variable)
                            -> (p,q : HsIdentVarLv x y)
                            -> p = q
lemma_HsIdentVarLv_singleton (HsIdentVar lv _ _) MkHsIdentVarLv MkHsIdentVarLv = Refl

data HsIdentVarId : (na : HsNameTy Variable) -> (id : Nat) -> Type where
  MkHsIdentVarId : HsIdentVarId (HsIdentVar _ id _) id

data HsIdentVarNa : (na : HsNameTy Variable) -> (na : Name Variable) -> Type where
  MkHsIdentVarNa : HsIdentVarNa (HsIdentVar _ _ na) na

getHsIdentVarName : (na : HsNameTy Variable) -> Subset (Name Variable) (HsIdentVarNa na)
getHsIdentVarName (HsIdentVar _ _ na) = Element na MkHsIdentVarNa

data SameLevel : (vars : Vect nvars (HsNameTy Variable)) -> Type where
  Vacuous     : SameLevel []
  MkSameLevel : (restSameLv : All (HsIdentVarLv lv) vars)
             -> SameLevel ((HsIdentVar lv _ _) :: vars)

decSameLevel : (vars : Vect nvars (HsNameTy Variable)) -> Dec (SameLevel vars)
decSameLevel [] = Yes Vacuous
decSameLevel (HsIdentVar lv _ _ :: vars) with (decAll (decHsIdentVarLv lv) vars)
  | No nok = No (\(MkSameLevel ok) => nok ok)
  | Yes ok = Yes (MkSameLevel ok)

lemma_SameLevel_singleton : (p,q : SameLevel xs) -> p = q
lemma_SameLevel_singleton Vacuous Vacuous = Refl
lemma_SameLevel_singleton (MkSameLevel p) (MkSameLevel q) =
  case lemma_All_singleton lemma_HsIdentVarLv_singleton p q of
    Refl => Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Equality.DecEq (HsNameTy Variable) where
  decEq (HsIdentVar p1 p2 p3) (HsIdentVar q1 q2 q3) with (decEq p1 q1)
    decEq (HsIdentVar p1 p2 p3) (HsIdentVar q1 q2 q3) | No neq = No (\Refl => neq Refl)
    decEq (HsIdentVar q1 p2 p3) (HsIdentVar q1 q2 q3) | Yes Refl with (decEq p2 q2)
      decEq (HsIdentVar q1 p2 p3) (HsIdentVar q1 q2 q3) | Yes Refl | No neq = No (\Refl => neq Refl)
      decEq (HsIdentVar q1 q2 p3) (HsIdentVar q1 q2 q3) | Yes Refl | Yes Refl with (decEq p3 q3)
        decEq (HsIdentVar q1 q2 p3) (HsIdentVar q1 q2 q3) | Yes Refl | Yes Refl | No neq =
          No (\Refl => neq Refl)
        decEq (HsIdentVar q1 q2 q3) (HsIdentVar q1 q2 q3) | Yes Refl | Yes Refl | Yes Refl =
          Yes Refl
