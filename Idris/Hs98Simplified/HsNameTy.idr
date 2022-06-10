module Hs98Simplified.HsNameTy

import IdrisUtils.Utils

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
data SHsNameTy : Type where
  SHsIdentVar : (lv : Nat) -> (id : Nat)  -> SHsNameTy
  SHsIdentCtr : (id : Nat)  -> SHsNameTy


--- [DecEq] ---

implementation Uninhabited (SHsIdentVar _ _ = SHsIdentCtr _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsIdentCtr _ = SHsIdentVar _ _) where
  uninhabited Refl impossible

implementation Equality.DecEq SHsNameTy where
  decEq (SHsIdentVar lv1 id1) (SHsIdentVar lv2 id2) with (decEq lv1 lv2)
    decEq (SHsIdentVar lv1 id1) (SHsIdentVar lv2 id2) | No neq = No (\Refl => neq Refl)
    decEq (SHsIdentVar lv1 id1) (SHsIdentVar lv1 id2) | Yes Refl with (decEq id1 id2)
      decEq (SHsIdentVar lv1 id1) (SHsIdentVar lv1 id2) | Yes Refl | No neq = No (\Refl => neq Refl)
      decEq (SHsIdentVar lv1 id1) (SHsIdentVar lv1 id1) | Yes Refl | Yes Refl = Yes Refl 

  decEq (SHsIdentCtr id1) (SHsIdentCtr id2) with (decEq id1 id2) 
    decEq (SHsIdentCtr id1) (SHsIdentCtr id2) | No neq = No (\Refl => neq Refl)
    decEq (SHsIdentCtr id1) (SHsIdentCtr id1) | Yes Refl = Yes Refl

  decEq (SHsIdentCtr id1) (SHsIdentVar lv id) = No absurd
  decEq (SHsIdentVar lv id) (SHsIdentCtr id2) = No (absurd . sym)

