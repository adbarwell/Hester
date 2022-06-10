module Hs98Simplified.HsDeclTy

import IdrisUtils.Utils
import IdrisUtils.Ord

import Hs98Simplified.HsNameTy
import Hs98Simplified.HsPatTy
import Hs98Simplified.HsExpTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data SHsDeclKindTy : Type where
  ||| HsDeclTy
  SDecl     : SHsDeclKindTy
  ||| HsMatchTy
  SFunClause : SHsDeclKindTy

implementation Uninhabited (SDecl = SFunClause) where
  uninhabited Refl impossible

decEqSHsDeclKindTy : (x,y : SHsDeclKindTy) -> Dec (x = y)
decEqSHsDeclKindTy SDecl SDecl = Yes Refl 
decEqSHsDeclKindTy SFunClause SFunClause = Yes Refl 
decEqSHsDeclKindTy SDecl SFunClause = No absurd
decEqSHsDeclKindTy SFunClause SDecl = No (absurd . sym)

implementation Equality.DecEq SHsDeclKindTy where
  decEq = decEqSHsDeclKindTy

||| Declarations.
|||
||| Declarations are indexed by a declaration kind, allowing us to flatten declarations and, e.g.,
||| function clauses, and thus avoid the totality or decidability problems encountered when
||| a representation closer to that which is used by `language-src` was defined.
data SHsDeclTy : (kind : SHsDeclKindTy) -> Type where
  ||| Function clauses.
  |||
  SHsMatch   : (ps : Vect (S nps) SHsPatTy)
            -> (e  : SHsExpTy)
            -> (ws : Vect nws (SHsDeclTy SDecl))
            -> SHsDeclTy SFunClause
  ||| Function declarations.
  |||
  SHsFunBind : (fname   : SHsNameTy)
            -> (clauses : Vect (S nclauses) (SHsDeclTy SFunClause))
            -> SHsDeclTy SDecl
  ||| Pattern bindings.
  |||
  SHsPatBind : (p  : SHsPatTy)
            -> (e  : SHsExpTy)
            -> (ws : Vect nws (SHsDeclTy SDecl))
            -> SHsDeclTy SDecl

implementation Uninhabited (SHsFunBind _ _ = SHsPatBind _ _ _) where
  uninhabited Refl impossible

implementation Equality.DecEq (SHsDeclTy kind) where
  decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps2 e2 ws2) with (decEqVect ps1 ps2)
    decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps2 e2 ws2) | No neq = No (\Refl => neq Refl)
    decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps1 e2 ws2) | Yes Refl with (decEq e1 e2)
      decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps1 e2 ws2) | Yes Refl | No neq = No (\Refl => neq Refl)
      decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps1 e1 ws2) | Yes Refl | Yes Refl with (assert_total (decEqVect ws1 ws2))
        decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps1 e1 ws2) | Yes Refl | Yes Refl | No neq =
          No (\Refl => neq Refl)
        decEq (SHsMatch ps1 e1 ws1) (SHsMatch ps1 e1 ws1) | Yes Refl | Yes Refl | Yes Refl =
          Yes Refl

  decEq (SHsFunBind fname1 clauses1) (SHsFunBind fname2 clauses2) with (decEq fname1 fname2)
    decEq (SHsFunBind fname1 clauses1) (SHsFunBind fname2 clauses2) | No neq = No (\Refl => neq Refl)
    decEq (SHsFunBind fname1 clauses1) (SHsFunBind fname1 clauses2) | Yes Refl with (assert_total (decEqVect clauses1 clauses2))
      decEq (SHsFunBind fname1 clauses1) (SHsFunBind fname1 clauses2) | Yes Refl | No neq = No (\Refl => neq Refl)
      decEq (SHsFunBind fname1 clauses1) (SHsFunBind fname1 clauses1) | Yes Refl | Yes Refl = Yes Refl 

  decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p2 e2 ws2) with (decEq p1 p2)
    decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p2 e2 ws2) | No neq = No (\Refl => neq Refl)
    decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p1 e2 ws2) | Yes Refl with (decEq e1 e2)
      decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p1 e2 ws2) | Yes Refl | No neq = No (\Refl => neq Refl)
      decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p1 e1 ws2) | Yes Refl | Yes Refl with (assert_total (decEqVect ws1 ws2))
        decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p1 e1 ws2) | Yes Refl | Yes Refl | No neq = No (\Refl => neq Refl)
        decEq (SHsPatBind p1 e1 ws1) (SHsPatBind p1 e1 ws1) | Yes Refl | Yes Refl | Yes Refl = Yes Refl 

  decEq (SHsFunBind v w) (SHsPatBind x y z) = No absurd
  decEq (SHsPatBind x y z) (SHsFunBind v w) = No (absurd . sym)
