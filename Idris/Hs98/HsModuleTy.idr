module Hs98.HsModuleTy

import IdrisUtils.Utils
import IdrisUtils.Ord

import Hs98.HsEnv
import Hs98.HsNameTy
import Hs98.HsPatTy
import Hs98.HsExpTy
import Hs98.HsDeclTy

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
data HsModuleTy : Type where
  |||
  ||| @env    the initial environment
  ||| @vars   the list of all variables exposed by, and shared between, the declarations in this 
  |||         module
  ||| @env_ds the initial environment extended with the variables exposed by the declarations in 
  |||         this module
  ||| @decls  the list of declarations that comprise this module
  HsModule : (env        : Env)
          -> (vars       : Vect (S nvars) (HsNameTy Variable))
          -> {sl         : SameLevel vars}
          -> {envRenv_ds : EnvAddNewLevel env vars sl env_ds}
          -> (decls      : Vect (S ndecls) (HsDeclTy env_ds (Decl vars sl)))
          -> HsModuleTy

---------------------------------------------------------------------------------------------------
-- [Names in Modules] -----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that a variable is declared in the given module.
data DecldHsModuleTy : (lvl : Nat) -> (id : Nat) -> (v : Name Variable) -> (m : HsModuleTy) -> Type where
  There : (later : DecldVectHsDeclTy lvl id v decls)
       -> DecldHsModuleTy lvl id v (HsModule env vars decls)

isDecldHsModuleTy : (lvl : Nat)
                 -> (id : Nat)
                 -> (v : Name Variable)
                 -> (m : HsModuleTy)
                 -> Basics.Dec (DecldHsModuleTy lvl id v m)
isDecldHsModuleTy lvl id v (HsModule _ _ ds) with (isDecldVectHsDeclTy lvl id v ds)
  isDecldHsModuleTy lvl id v (HsModule _ _ ds) | Yes later = Yes (There later)
  isDecldHsModuleTy lvl id v (HsModule _ _ ds) | No contra = No (\(There later) => contra later)
