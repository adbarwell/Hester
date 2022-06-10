module Hs98Simplified.HsExpTy

import IdrisUtils.Utils
import Hs98Simplified.HsNameTy
import Hs98Simplified.HsPatTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [AST] ------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data SHsLiteralTy : Type where
  SHsInt : Integer -> SHsLiteralTy


implementation Equality.DecEq SHsLiteralTy where
  decEq (SHsInt x) (SHsInt y) =
    case decEq x y of 
      Yes Refl => Yes Refl
      No neq => No (\Refl => neq Refl)

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Haskell Expressions
|||
data SHsExpTy :  Type where
  SHsVar      : (na : SHsNameTy) -> SHsExpTy
  SHsLit      : (li : SHsLiteralTy) -> SHsExpTy 
  SHsApp      : (f  : SHsExpTy) -> (e : SHsExpTy) -> SHsExpTy
  SHsLambda   : (ps : Vect (S nps) SHsPatTy) -> (e : SHsExpTy) -> SHsExpTy 
  SHsParen    : (e  : SHsExpTy) -> SHsExpTy

---------------------------------------------------------------------------------------------------
-- [Names in Expressions] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Uninhabited (SHsVar _ = SHsLit _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsVar _ = SHsApp _ _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsVar _ = SHsLambda _ _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsVar _ = SHsParen _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsLit _ = SHsApp _ _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsLit _ = SHsLambda _ _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsLit _ = SHsParen _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsApp _ _ = SHsLambda _ _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsApp _ _ = SHsParen _) where
  uninhabited Refl impossible
implementation Uninhabited (SHsLambda _ _ = SHsParen _) where
  uninhabited Refl impossible

decEqHsExpTy : (x,y : SHsExpTy) -> Dec (x = y)
decEqHsExpTy (SHsVar na) (SHsVar na2) with  (decEq na na2)
  decEqHsExpTy (SHsVar na) (SHsVar na2) | No neq = No (\Refl => neq Refl)
  decEqHsExpTy (SHsVar na) (SHsVar na) | Yes Refl = Yes Refl
decEqHsExpTy (SHsLit li1) (SHsLit li2) with (decEq li1 li2)
  decEqHsExpTy (SHsLit li1) (SHsLit li2) | No neq = No (\Refl => neq Refl)
  decEqHsExpTy (SHsLit li1) (SHsLit li1) | Yes Refl = Yes Refl
decEqHsExpTy (SHsApp e1 e2) (SHsApp e3 e4) with (decEqHsExpTy e1 e3)
  decEqHsExpTy (SHsApp e1 e2) (SHsApp e3 e4) | No neq = No (\Refl => neq Refl)
  decEqHsExpTy (SHsApp e1 e2) (SHsApp e1 e4) | Yes Refl with (decEqHsExpTy e2 e4) 
    decEqHsExpTy (SHsApp e1 e2) (SHsApp e1 e4) | Yes Refl | No neq = No (\Refl => neq Refl)
    decEqHsExpTy (SHsApp e1 e2) (SHsApp e1 e2) | Yes Refl | Yes Refl = Yes Refl 
decEqHsExpTy (SHsLambda ps1 e1) (SHsLambda ps2 e2) with (decEqVect ps1 ps2)
  decEqHsExpTy (SHsLambda ps1 e1) (SHsLambda ps2 e2) | No neq = No (\Refl => neq Refl)
  decEqHsExpTy (SHsLambda ps1 e1) (SHsLambda ps1 e2) | Yes Refl with (decEqHsExpTy e1 e2)
    decEqHsExpTy (SHsLambda ps1 e1) (SHsLambda ps1 e2) | Yes Refl | No neq = No (\Refl => neq Refl)
    decEqHsExpTy (SHsLambda ps1 e1) (SHsLambda ps1 e1) | Yes Refl | Yes Refl = Yes Refl 
decEqHsExpTy (SHsParen e1) (SHsParen e2) with (decEqHsExpTy e1 e2) 
  decEqHsExpTy (SHsParen e1) (SHsParen e2) | No neq = No (\Refl => neq Refl)
  decEqHsExpTy (SHsParen e1) (SHsParen e1) | Yes Refl = Yes Refl

decEqHsExpTy (SHsVar na) (SHsLit li) = No absurd
decEqHsExpTy (SHsVar na) (SHsApp f e) = No absurd
decEqHsExpTy (SHsVar na) (SHsLambda ps e) = No absurd
decEqHsExpTy (SHsVar na) (SHsParen e) = No absurd
decEqHsExpTy (SHsLit li) (SHsVar na) = No (absurd . sym)
decEqHsExpTy (SHsLit li) (SHsApp f e) = No absurd
decEqHsExpTy (SHsLit li) (SHsLambda ps e) = No absurd
decEqHsExpTy (SHsLit li) (SHsParen e) = No absurd
decEqHsExpTy (SHsApp f e) (SHsVar na) = No (absurd . sym)
decEqHsExpTy (SHsApp f e) (SHsLit li) = No (absurd . sym)
decEqHsExpTy (SHsApp f e) (SHsLambda ps g) = No absurd
decEqHsExpTy (SHsApp f e) (SHsParen g) = No absurd
decEqHsExpTy (SHsLambda ps e) (SHsVar na) = No (absurd . sym)
decEqHsExpTy (SHsLambda ps e) (SHsLit li) = No (absurd . sym)
decEqHsExpTy (SHsLambda ps e) (SHsApp f g) = No (absurd . sym)
decEqHsExpTy (SHsLambda ps e) (SHsParen g) = No absurd
decEqHsExpTy (SHsParen e) (SHsVar na) = No (absurd . sym)
decEqHsExpTy (SHsParen e) (SHsLit li) = No (absurd . sym)
decEqHsExpTy (SHsParen e) (SHsApp f g) = No (absurd . sym)
decEqHsExpTy (SHsParen e) (SHsLambda ps f) = No (absurd . sym)


implementation Equality.DecEq SHsExpTy where
  decEq = decEqHsExpTy
