module Hs98Simplified.HsModuleTy

import IdrisUtils.Utils
import IdrisUtils.Ord

import Hs98Simplified.HsNameTy
import Hs98Simplified.HsPatTy
import Hs98Simplified.HsExpTy
import Hs98Simplified.HsDeclTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A module is a list of mutually defined declarations.
|||
||| For simplicity, we assume neither imports nor exports at this current stage.
||| Thus, a Haskell program is a single module.
||| Constructors and operator names declared in the Prelude are 'preloaded' in the initial 
||| environment.
|||
data SHsModuleTy : Type where
  SHsModule : (decls : Vect (S ndecls) (SHsDeclTy SDecl)) -> SHsModuleTy

implementation Equality.DecEq SHsModuleTy where
  decEq (SHsModule decls1) (SHsModule decls2) with (decEqVect decls1 decls2)
    decEq (SHsModule decls1) (SHsModule decls2) | No neq = No (\Refl => neq Refl)
    decEq (SHsModule decls1) (SHsModule decls1) | Yes Refl = Yes Refl 

