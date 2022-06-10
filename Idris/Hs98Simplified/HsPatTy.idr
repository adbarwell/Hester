module Hs98Simplified.HsPatTy

import IdrisUtils.Utils
import IdrisUtils.Ord
import IdrisUtils.Decidability
import IdrisUtils.Data.Vect

import Hs98Simplified.HsNameTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Pattern Contents] -----------------------------------------------------------------------------

||| Represents a flattened pattern definition. A pattern's children (if any) are referenced using a
||| finite set that refers to a position in the list of all flattened pattern definitions.
data SHsPatDefTy : Type where
  SHsPVar : (na : SHsNameTy) -> SHsPatDefTy
  SHsPApp : (args : Vect nargs (Fin n)) -> SHsPatDefTy

implementation Uninhabited (SHsPApp _ = SHsPVar _) where
  uninhabited Refl impossible

decEqHsPatDefTy : (x,y : SHsPatDefTy) -> Dec (x = y)
decEqHsPatDefTy (SHsPVar na1) (SHsPVar na2) with (decEq na1 na2)
  decEqHsPatDefTy (SHsPVar na1) (SHsPVar na2) | No neq = No (\Refl => neq Refl)
  decEqHsPatDefTy (SHsPVar na1) (SHsPVar na1) | Yes Refl = Yes Refl 
decEqHsPatDefTy (SHsPApp {n=n1} args1) (SHsPApp {n=n2} args2) with (decEq n1 n2)
  decEqHsPatDefTy (SHsPApp {n=n1} args1) (SHsPApp {n=n2} args2) | No neq = No (\Refl => neq Refl)
  decEqHsPatDefTy (SHsPApp {n=n1} args1) (SHsPApp {n=n1} args2) | Yes Refl with (decEqVect args1 args2)
    decEqHsPatDefTy (SHsPApp {n=n1} args1) (SHsPApp {n=n1} args2) | Yes Refl | No neq =
      No (\Refl => neq Refl)
    decEqHsPatDefTy (SHsPApp {n=n1} args1) (SHsPApp {n=n1} args1) | Yes Refl | Yes Refl =
      Yes Refl 
decEqHsPatDefTy (SHsPApp args) (SHsPVar na) = No absurd
decEqHsPatDefTy (SHsPVar na) (SHsPApp args) = No (absurd . sym)


implementation Equality.DecEq SHsPatDefTy where
  decEq = decEqHsPatDefTy

data SHsPatTy : Type where
  SHsPat : (defs : Vect (S n) SHsPatDefTy) -> SHsPatTy

implementation Equality.DecEq SHsPatTy where
  decEq (SHsPat defs1) (SHsPat defs2) with (decEqVect defs1 defs2)
    decEq (SHsPat defs1) (SHsPat defs2) | No neq = No (\Refl => neq Refl)
    decEq (SHsPat defs1) (SHsPat defs1) | Yes Refl = Yes Refl 


