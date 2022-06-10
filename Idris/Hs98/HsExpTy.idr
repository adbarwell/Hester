module Hs98.HsExpTy

import IdrisUtils.Utils
import Hs98.HsEnv
import Hs98.HsNameTy
import Hs98.HsPatTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [AST] ------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HsLiteralTy : Type where
  HsInt : Integer -> HsLiteralTy

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Haskell Expressions
|||
||| Indexed by an envrionment.
data HsExpTy : (env : Env) -> Type where
  HsVar      : (na : HsNameTy Variable) -> {ok : ElemEnv env na} -> HsExpTy env
  HsLit      : (li : HsLiteralTy) -> HsExpTy env
  HsApp      : (f : HsExpTy env) -> (e : HsExpTy env) -> HsExpTy env
  HsLambda   : (ps   : Vect (S nps) (HsPatTy env))
            -> {psec : HsPatSecTy env ps env_e}
            -> (e    : HsExpTy env_e)
            -> HsExpTy env
  HsParen    : (e : HsExpTy env) -> HsExpTy env

---------------------------------------------------------------------------------------------------
-- [Names in Expressions] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that a variable is declared in an expression.
data DecldHsExpTy : (lvl : Nat) -> (id : Nat) -> (v : Name Variable) -> (e : HsExpTy env) -> Type where
  HereLambda  : (there : DecldVectHsPatTy lvl id v ps) -> DecldHsExpTy lvl id v (HsLambda ps e)

  ThereAppF   : (there : DecldHsExpTy lvl id v f) -> DecldHsExpTy lvl id v (HsApp f e)
  ThereAppE   : (there : DecldHsExpTy lvl id v e) -> DecldHsExpTy lvl id v (HsApp f e)
  ThereLambda : (there : DecldHsExpTy lvl id v e) -> DecldHsExpTy lvl id v (HsLambda ps e)
  ThereParen  : (there : DecldHsExpTy lvl id v e) -> DecldHsExpTy lvl id v (HsParen e)

implementation Uninhabited (DecldHsExpTy lvl id v (HsVar n)) where
    uninhabited HereLambda impossible
    uninhabited ThereAppF impossible
    uninhabited ThereAppE impossible
    uninhabited ThereLambda impossible
    uninhabited ThereParen impossible

implementation Uninhabited (DecldHsExpTy lvl id v (HsLit n)) where
  uninhabited HereLambda impossible
  uninhabited ThereAppF impossible
  uninhabited ThereAppE impossible
  uninhabited ThereLambda impossible
  uninhabited ThereParen impossible

isDecldHsExpTy : (lvl : Nat) -> (id : Nat) -> (v : Name Variable) -> (e : HsExpTy env) -> Dec (DecldHsExpTy lvl id v e)
isDecldHsExpTy lvl id v (HsVar (HsIdentVar lv id' na)) = No absurd
isDecldHsExpTy lvl id v (HsLit _) = No absurd

isDecldHsExpTy lvl id v (HsApp f e) with (isDecldHsExpTy lvl id v f)
  isDecldHsExpTy lvl id v (HsApp f e) | Yes prf = Yes (ThereAppF prf)
  isDecldHsExpTy lvl id v (HsApp f e) | No contra_f with (isDecldHsExpTy lvl id v e)
    isDecldHsExpTy lvl id v (HsApp f e) | No contra_f | Yes prf = Yes (ThereAppE prf)
    isDecldHsExpTy lvl id v (HsApp f e) | No contra_f | No contra_e = No (contra contra_f contra_e) 
      where
        contra : (np1 : Not (DecldHsExpTy lvl id v f))
              -> (np2 : Not (DecldHsExpTy lvl id v e))
              -> Not (DecldHsExpTy lvl id v (HsApp f e))
        contra np1 np2 (ThereAppF p1) = np1 p1
        contra np1 np2 (ThereAppE p2) = np2 p2

isDecldHsExpTy lvl id v (HsLambda ps e) with (isDecldVectHsPatTy lvl id v ps)
  isDecldHsExpTy lvl id v (HsLambda ps e) | Yes prf = Yes (HereLambda prf)
  isDecldHsExpTy lvl id v (HsLambda ps e) | No contra_ps with (isDecldHsExpTy lvl id v e)
    isDecldHsExpTy lvl id v (HsLambda ps e) | No contra_ps | Yes prf = Yes (ThereLambda prf)
    isDecldHsExpTy lvl id v (HsLambda ps e) | No contra_ps | No contra_e =
      No (contra contra_ps contra_e) where

        contra : (np1 : Not (DecldVectHsPatTy lvl id v ps))
              -> (np2 : Not (DecldHsExpTy lvl id v e))
              -> Not (DecldHsExpTy lvl id v (HsLambda ps e))
        contra np1 np2 (HereLambda p1) = np1 p1
        contra np1 np2 (ThereLambda p2) = np2 p2

isDecldHsExpTy lvl id v (HsParen e) with (isDecldHsExpTy lvl id v e)
  isDecldHsExpTy lvl id v (HsParen e) | Yes prf = Yes (ThereParen prf)
  isDecldHsExpTy lvl id v (HsParen e) | No contra = No (\(ThereParen p) => contra p)
