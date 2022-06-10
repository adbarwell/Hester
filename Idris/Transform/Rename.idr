module Transform.Rename

import Transform.Rename.SSimplification
import HaReRenaming

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data StructEq : (m1, m2: HsModuleTy) -> Type where
  MkStructEq : (p : Struct m1 m1s) -> (q : Struct m2 m2s) -> (eq : m1s = m2s) -> StructEq m1 m2
            
data RenamePrf : (lv,id : Nat) 
              -> (oldN,newN : Name Variable) 
              -> (m1 : HsModuleTy) 
              -> (r : ErrorOr
                        (DecldHsModuleTy lvl id oldN m1,
                         (m2 : HsModuleTy **  (StructEq m1 m2, DecldHsModuleTy lvl id newN m2))))
             -> Type where
  RenameFail : RenamePrf lv id oldN newN m1 (Err err)
  RenameSucc : (oldD : DecldHsModuleTy lv id oldN m1)
            -> (newD : DecldHsModuleTy lv id newN m2)
            -> (eq : StructEq m1 m2)
            -> RenamePrf lv id oldN newN m1 (Just (oldD, (m2 ** (eq,newD)))) 

rename' : (lv, id : Nat)
       -> (oldN,newN : HsNameTy Variable)
       -> (m1 : HsModuleTy)
       -> ErrorOr (m2 : HsModuleTy ** StructEq m1 m2)
rename' lv id oldN newN m1 with (transStructModule m1)
  | (m1s ** m1sP) =
    case renameModule lv id oldN newN m1 of
      Err err => Err err
      Just m2 => case transStructModule m2 of
        (m2s ** m2sP) => case decEq m1s m2s of
          No neq => Err (TyErr ("rename'.decEq", m1s, m2s, neq))
          Yes Refl => Just (m2 ** MkStructEq m1sP m2sP Refl)

rename : (lv,id : Nat) 
      -> (oldN,newN : Name Variable) 
      -> (m1 : HsModuleTy)
      -> ErrorOr
            (DecldHsModuleTy lv id oldN m1,
             (m2 : HsModuleTy ** (StructEq m1 m2, DecldHsModuleTy lv id newN m2)))
rename lv id oldN newN m1 =
  let oldV = HsIdentVar lv id oldN
      newV = HsIdentVar lv id newN in
  case isDecldHsModuleTy lv id oldN m1 of
    No np => Err (TyErr ("rename.isDecldHsModuleTy.oldN", lv, id, oldN, np, m1))
    Yes oldD =>
      case rename' lv id oldV newV m1 of
        Err err => Err err
        Just (m2 ** eq) =>
          case isDecldHsModuleTy lv id newN m2 of
            No np => Err (TyErr ("rename.isDecldHsModuleTy.newN", lv, id, newN, np, m2))
            Yes newD => Just (oldD, (m2 ** (eq, newD)))

decStructEq : (m1,m2 : HsModuleTy) -> Basics.Dec (StructEq m1 m2)
decStructEq m1 m2 =
  case transStructModule m1 of 
    (m1' ** m1Prf) => 
      case transStructModule m2 of 
        (m2' ** m2Prf) =>
          case decEq m1' m2' of 
            Yes Refl => Yes (MkStructEq m1Prf m2Prf Refl)
            No neq => No (\(MkStructEq {m1s=x} {m2s=y} p1 p2 p3) =>
                              case inj m1 m1' x m1Prf p1 of
                                Refl => case inj m2 m2' y m2Prf p2 of
                                  Refl => neq p3)

prfRename : (lv,id : Nat) 
         -> (oldN,newN : Name Variable) 
         -> (m1 : HsModuleTy) 
         -> RenamePrf lv id oldN newN m1 (rename lv id oldN newN m1)
prfRename lv id oldN newN m1 with (rename lv id oldN newN m1) 
  | Err err = RenameFail
  | Just (oldD, (m2 ** (eq, newD))) = RenameSucc oldD newD eq
