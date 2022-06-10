module Hs98.HsDeclTy

import IdrisUtils.Utils
import IdrisUtils.Ord

import Hs98.HsEnv
import Hs98.HsNameTy
import Hs98.HsPatTy
import Hs98.HsExpTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HsDeclKindTy : Type where
  ||| HsDeclTy
  Decl      : (vars   : Vect nvars (HsNameTy Variable))
           -> (sameLv : SameLevel vars)
           -> HsDeclKindTy
  ||| HsMatchTy
  FunClause : (npats  : Nat) -> HsDeclKindTy

||| Declarations.
|||
||| Declarations are indexed by a declaration kind, allowing us to flatten declarations and, e.g.,
||| function clauses, and thus avoid the totality or decidability problems encountered when
||| a representation closer to that which is used by `language-src` was defined.
data HsDeclTy : (env : Env) -> (kind : HsDeclKindTy) -> Type where
  ||| Function clauses.
  |||
  ||| For simplicity, we assume unguarded RHS for each function clause.
  ||| 
  |||
  ||| @env      the initial environment
  ||| @env_ws   the initial environment with all variables declared in the patterns
  ||| @env_e    the initial environment with both all variables declared in the patterns and
  |||           all function names and simple pattern variables in the where block
  ||| @vars_ws  the list of all variables in scope for the RHS defined in the where block
  HsMatch   : (ps      : Vect (S nps) (HsPatTy env))
           -> {psec    : HsPatSecTy env ps env_ws}
           -> {envUpd  : EnvAddNewLevel env_ws vars_ws sl_ws env_e}
           -> (e       : HsExpTy env_e)
           -> (ws      : Vect nws (HsDeclTy env_e (Decl vars_ws sl_ws)))
           -> HsDeclTy env (FunClause (S nps))
  ||| Function declarations.
  |||
  ||| @fnInEnv a proof that the name of the function is already in the environment; due to Haskell's
  |||          mutually-defined-by-default approach to declarations the name of the function
  |||          (and all other declarations of the same level) is added to the environment at the
  |||          level immediately above this declaration (i.e. the module or where block to/of which
  |||          this declaration belongs/is a sub-expression).
  ||| @vars    the list of all variables exposed by this and other declarations defined in the same
  |||          module or where block; the name of the function in this function declaration should
  |||          be a member
  ||| @npats   each clause must have the same (non-zero) number of patterns
  HsFunBind : (fname     : HsNameTy Variable)
           -> {fnInEnv   : ElemEnv env fname}
           -> {fnInVars  : Elem fname vars}
           -> (clauses   : Vect (S nclauses) (HsDeclTy env (FunClause (S npats))))
           -> HsDeclTy env (Decl vars sl)
  ||| Pattern bindings.
  |||
  ||| @env_e    the initial environment with both all variables declared in the patterns and
  |||           all function names and simple pattern variables in the where block
  ||| @vars    the list of all variables exposed by this and other declarations defined in the same
  |||          module or where block; the variables declared in the pattern should be members
  ||| @vars_ws  the list of all variables in scope for the RHS defined in the where block
  HsPatBind : (p       : HsPatTy env)
           -> {pInVars : HsPatTyElemVars p vars}
           -> {pInEnv  : HsPatTyElemEnv env p}
           -> {envUpd  : EnvAddNewLevel env vars_ws sl_ws env_e}
           -> (e       : HsExpTy env_e)
           -> (ws      : Vect nws (HsDeclTy env_e (Decl vars_ws sl_ws)))
           -> HsDeclTy env (Decl vars sl)

---------------------------------------------------------------------------------------------------
-- [Names in Declarations] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that a variable is declared in a list of declarations.
data DecldVectHsDeclTy : (lvl : Nat)
                      -> (id : Nat)
                      -> (v  : Name Variable)
                      -> (ds : Vect nds (HsDeclTy env dk))
                      -> Type where
  -- HsMatch
  HereMInPats  : (there : DecldVectHsPatTy lvl id v ps)
              -> DecldVectHsDeclTy lvl id v (HsMatch ps e ws :: ds)
  HereMInExp   : (there : DecldHsExpTy lvl id v e)
              -> DecldVectHsDeclTy lvl id v (HsMatch ps e ws :: ds)
  HereMInWhere : (there : DecldVectHsDeclTy lvl id v ws)
              -> DecldVectHsDeclTy lvl id v (HsMatch ps e ws :: ds)

  -- HsFunBind
  HereF          : DecldVectHsDeclTy lvl id na (HsFunBind (HsIdentVar lv id na) cs :: ds)
  HereFInClauses : (there : DecldVectHsDeclTy lvl id v cs)
                -> DecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv j na) cs :: ds)

  -- HsPatBind
  HerePInPat   : (there : DecldVectHsPatTy lvl id v [p])
              -> DecldVectHsDeclTy lvl id v (HsPatBind p e ws :: ds)
  HerePInExp   : (there : DecldHsExpTy lvl id v e)
              -> DecldVectHsDeclTy lvl id v (HsPatBind p e ws :: ds)
  HerePInWhere : (there : DecldVectHsDeclTy lvl id v ws)
              -> DecldVectHsDeclTy lvl id v (HsPatBind p e ws :: ds)

  -- Tail
  There : (later : DecldVectHsDeclTy lvl id v ds) -> DecldVectHsDeclTy lvl id v (d :: ds)

implementation Uninhabited (DecldVectHsDeclTy l i v []) where
  uninhabited HereMInPats impossible
  uninhabited HereMInExp impossible
  uninhabited HereMInWhere impossible
  uninhabited HereF impossible
  uninhabited HereFInClauses impossible
  uninhabited HerePInPat impossible
  uninhabited HerePInExp impossible
  uninhabited HerePInWhere impossible
  uninhabited There impossible

isDecldVectHsDeclTy : (lvl : Nat)
                   -> (id : Nat)
                   -> (v : Name Variable)
                   -> (ds : Vect nds (HsDeclTy env dk))
                   -> Dec (DecldVectHsDeclTy lvl id v ds)
isDecldVectHsDeclTy lvl id v [] = No absurd

isDecldVectHsDeclTy lvl id v (HsMatch ps e ws :: ds) with (isDecldVectHsPatTy lvl id v ps)
  | Yes prf = Yes (HereMInPats prf)
  | No contra_ps with (isDecldHsExpTy lvl id v e)
    | Yes prf = Yes (HereMInExp prf)
    | No contra_e with (isDecldVectHsDeclTy lvl id v ws)
      | Yes prf = Yes (HereMInWhere prf)
      | No contra_ws with (isDecldVectHsDeclTy lvl id v ds)
        | Yes prf = Yes (There prf)
        | No contra_ds =
          No (contra contra_ps contra_e contra_ws contra_ds) where
            
            contra : (np1 : Not (DecldVectHsPatTy lvl id v ps))
                  -> (np2 : Not (DecldHsExpTy lvl id v e))
                  -> (np3 : Not (DecldVectHsDeclTy lvl id v ws))
                  -> (np4 : Not (DecldVectHsDeclTy lvl id v ds))
                  -> Not (DecldVectHsDeclTy lvl id v (HsMatch ps e ws :: ds))
            contra np1 np2 np3 np4 (HereMInPats p1) = np1 p1
            contra np1 np2 np3 np4 (HereMInExp p2) = np2 p2
            contra np1 np2 np3 np4 (HereMInWhere p3) = np3 p3
            contra np1 np2 np3 np4 (There p4) = np4 p4

isDecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id' na) cs :: ds) with (decEq id id')
  isDecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id na) cs :: ds) | Yes Refl with (decEq v na)
    isDecldVectHsDeclTy lvl id na (HsFunBind (HsIdentVar lv id na) cs :: ds) | Yes Refl | Yes Refl = Yes HereF
    isDecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id na) cs :: ds) | Yes Refl | No neq
      with (isDecldVectHsDeclTy lvl id v cs)
        | Yes prf = Yes (HereFInClauses prf)
        | No contra_cs with (isDecldVectHsDeclTy lvl id v ds)
          | Yes prf = Yes (There prf)
          | No contra_ds = No (contra neq contra_cs contra_ds) where

            contra : (np1 : Not (v = w))
                  -> (np2 : Not (DecldVectHsDeclTy lvl id v cs))
                  -> (np3 : Not (DecldVectHsDeclTy lvl id v ds))
                  -> Not (DecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id w) cs :: ds))
            contra np1 np2 np3 HereF = np1 Refl
            contra np1 np2 np3 (HereFInClauses p2) = np2 p2
            contra np1 np2 np3 (There p3) = np3 p3

  isDecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id' na) cs :: ds) | No neq
    with (isDecldVectHsDeclTy lvl id v cs)
      | Yes prf = Yes (HereFInClauses prf)
      | No contra_cs with (isDecldVectHsDeclTy lvl id v ds)
        | Yes prf = Yes (There prf)
        | No contra_ds = No (contra neq contra_cs contra_ds) where

          contra : {id  : Nat}
                -> (np1 : Not (id = id'))
                -> (np2 : Not (DecldVectHsDeclTy lvl id v cs))
                -> (np3 : Not (DecldVectHsDeclTy lvl id v ds))
                -> Not (DecldVectHsDeclTy lvl id v (HsFunBind (HsIdentVar lv id' w) cs :: ds))
          contra np1 np2 np3 HereF = np1 Refl
          contra np1 np2 np3 (HereFInClauses p2) = np2 p2
          contra np1 np2 np3 (There p3) = np3 p3

isDecldVectHsDeclTy lvl id v (HsPatBind p e ws :: ds) with (isDecldVectHsPatTy lvl id v [p])
  | Yes prf = Yes (HerePInPat prf)
  | No contra_p with (isDecldHsExpTy lvl id v e)
    | Yes prf = Yes (HerePInExp prf)
    | No contra_e with (isDecldVectHsDeclTy lvl id v ws)
      | Yes prf = Yes (HerePInWhere prf)
      | No contra_ws with (isDecldVectHsDeclTy lvl id v ds)
        | Yes prf = Yes (There prf)
        | No contra_ds = No (contra contra_p contra_e contra_ws contra_ds) where

          contra : (np1 : Not (DecldVectHsPatTy lvl id v [p]))
                -> (np2 : Not (DecldHsExpTy lvl id v e))
                -> (np3 : Not (DecldVectHsDeclTy lvl id v ws))
                -> (np4 : Not (DecldVectHsDeclTy lvl id v ds))
                -> Not (DecldVectHsDeclTy lvl id v (HsPatBind p e ws :: ds))
          contra np1 np2 np3 np4 (HerePInPat p1) = np1 p1
          contra np1 np2 np3 np4 (HerePInExp p2) = np2 p2
          contra np1 np2 np3 np4 (HerePInWhere p3) = np3 p3
          contra np1 np2 np3 np4 (There p4) = np4 p4
