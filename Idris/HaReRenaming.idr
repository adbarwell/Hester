module HaReRenaming

import Hs98

import public Error

%default total
%access public export

myMap : (f : a -> ErrorOr b) -> Vect n a -> ErrorOr (Vect n b)
-- myMap f xs = sequence (Functor.map f xs)
myMap f [] = Just []
myMap f (x :: xs) with (f x)
  | Err err = Err err
  | Just x' with (myMap f xs)
    | Err err = Err err
    | Just xs' = Just (x' :: xs')

updateVars : (newName : (HsNameTy Variable))
          -> (oldVars : Vect k (HsNameTy Variable) )
          -> (Vect k (HsNameTy Variable))
updateVars newName []  = []
updateVars (HsIdentVar lv id na) ((HsIdentVar lv2 id2 na2)::xs)  =
  case decEq lv lv2 of
    Yes p => 
      case decEq id id2 of 
        Yes p1 => (HsIdentVar lv id na)::(updateVars (HsIdentVar lv id na) xs )
        No _ => (HsIdentVar lv2 id2 na2)::(updateVars (HsIdentVar lv id na) xs )
    No _ => (HsIdentVar lv2 id2 na2)::(updateVars (HsIdentVar lv id na) xs )

transformLevel :  (vars : Vect nvars (EnvItem Variable))
               -> (oldNa : HsNameTy Variable)
               -> (na : EnvItem Variable)
               -> ErrorOr (Vect nvars (EnvItem Variable))
transformLevel [] oldNa na = Err (StdErr "transformLevel []")
transformLevel ((MkEnvItem id x) :: xs) (HsIdentVar lv id2 n) (MkEnvItem id3 na) = 
  case (decEq id id2) of
    Yes Refl => Just ((MkEnvItem id na) :: xs) 
    No  neq_n => case (transformLevel xs (HsIdentVar lv id2 n) (MkEnvItem id3 na)) of
      Err err => Err (TyErr ("transformLevel", neq_n, err))
      Just ve => Just ((MkEnvItem id x)::ve)

transformScopeLevel : (lvls : Vect nlvls ScopeLevel) 
                   -> (oldNa : HsNameTy Variable) 
                   -> (na : EnvItem Variable)
                   -> ErrorOr (Vect nlvls ScopeLevel)
transformScopeLevel [] (HsIdentVar lv id n) na = 
  Just []
transformScopeLevel (MkScopeLevel slv vars {lin} :: lvls) (HsIdentVar lv id n) na = 
  case (decEq slv lv) of
    Yes Refl => case (transformLevel vars (HsIdentVar lv id n) na) of
      Just ve => case (decUniqueNames ve) of
        Yes lin2 => Just (MkScopeLevel lv ve {lin=lin2} :: lvls)
        No  no_u => Err (TyErr ("transformScopeLevel.decUniqueNames", no_u))
      Err err => Err err
    No  neq_lv => case (transformScopeLevel lvls (HsIdentVar lv id n) na) of
      Just scps => Just (MkScopeLevel slv vars {lin=lin} :: scps)
      Err err   => Err err

transformEnv : (oldEnv : Env) 
            -> (oldNa : HsNameTy nk) 
            -> (na : (EnvItem Variable)) 
            -> ErrorOr Env
transformEnv (MkEnv ctrs lvls) (HsIdentVar lv id na1) na = 
    case (transformScopeLevel lvls (HsIdentVar lv id na1) na) of
                    Just lvls2 => case (decUniqueIds ctrs lvls2) of
                                    Yes prf => Just (MkEnv {ok=prf} ctrs lvls2)
                                    No contra => Err (TyErr ("transformEnv.decUniqueIds", contra))
                    Err err    => Err err
transformEnv (MkEnv ctrs lvls) (HsIdentCtr id na1) na = Err (StdErr "transformEnv (HsIdentCtr)")

renamePatDefTy : (lv : Nat) 
            -> (id : Nat) 
            -> (transformedEnv : Env)
            -> (newName : (EnvItem Variable)) 
            -> (HsPatDefTy bound env) 
            -> ErrorOr (HsPatDefTy bound transformedEnv)
renamePatDefTy {bound} {env} lv id transformedEnv newName (HsPVar (HsIdentVar lv2 id2 na)) = 
  case decEq lv lv2 of
    Yes Refl => case decEq id id2 of 
      Yes Refl => case getEnvItemNa newName of
        Element na2 MkEnvItemNa => Just (HsPVar (HsIdentVar lv2 id2 na2))
      No cNEQid => Just (HsPVar (HsIdentVar lv2 id2 na))
    No  cNEQlv => Just (HsPVar (HsIdentVar lv2 id2 na))
renamePatDefTy {bound} {env} lv id transformedEnv newName (HsPApp {ctrKnown=ctrKnown} ctr args) =
  case isElemEnv transformedEnv ctr of
    Yes p => Just (HsPApp {ctrKnown=p} ctr args)
    No  c => Err (TyErr ("renamePatDefTy.isElemEnv", c))
 


renamePatsDefTy :  (lv : Nat)
              -> (id : Nat)
              -> (transformedEnv : Env)
              -> (newName : (EnvItem Variable)) 
              -> (ps      : Vect (S nps) (HsPatDefTy bound env))
              -> ErrorOr (Vect (S nps) (HsPatDefTy bound transformedEnv))
renamePatsDefTy lvl id transformedEnv newName (p :: []) =    
  case renamePatDefTy lvl id transformedEnv newName p of
    Err err => Err err
    Just p' => Just (p'::[]) 
renamePatsDefTy lvl id transformedEnv newName (p :: (p2::ps)) = 
  case renamePatDefTy lvl id transformedEnv newName p of
    Err err => Err err
    Just p' => case renamePatsDefTy lvl id transformedEnv newName (p2::ps) of 
                Err err => Err err
                Just (p2'::ps') => Just (p'::(p2'::ps'))

renamePatTy : (lv, id : Nat)
           -> (oldN, newN : Name Variable)
           -> (env : Env)
           -> (ps   : Vect (S nps) (HsPatTy env0))
           -> ErrorOr (Vect (S nps) (HsPatTy env))
renamePatTy lvl id oldN newN env ((HsPat {ok=newok} d)::[]) = 
  case (renamePatsDefTy lvl id env (MkEnvItem id newN) d) of
    Err err => Err err 
    Just (p'::ps') => case (decIsTree (p'::ps')) of
      No c    => Err (TyErr ("renamePatTy.decIsTree", c))
      Yes ok2 => Just ((HsPat {ok=ok2} (p'::ps'))::[])
renamePatTy lvl id oldN newN env ((HsPat {ok=newok} d)::(d'::defs')) = 
  case (renamePatsDefTy lvl id env (MkEnvItem id newN) d) of
    Err err => Err err 
    Just (p'::ps') => case (decIsTree (p'::ps')) of
      No np => Err (TyErr ("renamePatTy.decIsTree", np))
      Yes ok2 => case (renamePatTy lvl id oldN newN env (d'::defs')) of
        Err err => Err err
        Just (p2::ps2) => Just ((HsPat {ok=ok2} (p'::ps'))::(p2::ps2))


renamePatTySingle : (lvl : Nat)
                 -> (id : Nat)
                 -> (transformedEnv : Env)
                 -> (newName : (EnvItem Variable))
                 -> (p : HsPatTy env)
                 -> ErrorOr (HsPatTy transformedEnv)
renamePatTySingle lvl id transformedEnv newName (HsPat {ok=newok} d) =
  case renamePatsDefTy lvl id transformedEnv newName d of 
    Just (p'::ps') => case (decIsTree (p'::ps')) of
      Yes ok2 => Just (HsPat {ok=ok2} (p'::ps'))
      No c    => Err (TyErr ("renamePatTySingle.decIsTree", c))
    Err err => Err err 


  -- Two parts of renaming:
  --   1. the renaming has occurred and we have a new environment that we’re substituting
  --   2. the renaming has not occurred yet.

renameHsNameTy : (lv, id : Nat)
              -> (oldN, newN : Name Variable)
              -> (v : HsNameTy Variable)
              -> ErrorOr (HsNameTy Variable)
renameHsNameTy lv id oldN newN (HsIdentVar l i n) with (decEq id i)
  renameHsNameTy lv id oldN newN (HsIdentVar l i n) | No neq = Just (HsIdentVar l i n)
  renameHsNameTy lv id oldN newN (HsIdentVar l id n) | Yes Refl = Just (HsIdentVar lv id newN)

-- still looking for the binding instance of (lv,id,oldN)
renameExpr :  (lv : Nat)
           -> (id : Nat)
           -> (oldNa : Name Variable) 
           -> (newName : Name Variable)
           -> (env : Env)
           -> (exp : HsExpTy.HsExpTy initEnv)
           -> ErrorOr (HsExpTy.HsExpTy env)
renameExpr lv id oldN newN env (HsLit li) = Just (HsLit li) -- no renaming can occur here
renameExpr lv id oldN newN env (HsVar {ok} v) with (renameHsNameTy lv id oldN newN v)
  | Err err = Err err
  | Just v' with (isElemEnv env v')
    | No np = Err (TyErr ("renameExpr.isElemEnv", v', env, np))
    | Yes ok' = Just (HsVar {ok=ok'} v')
renameExpr lv id oldN newN env (HsApp e1 e2) with (renameExpr lv id oldN newN env e1)
  | Err err = Err err
  | Just e1' with (renameExpr lv id oldN newN env e2)
    | Err err = Err err
    | Just e2' = Just (HsApp e1' e2')

renameExpr lv id oldN newN env (HsLambda {env_e} {psec} ps e)
  with (renamePatTy lv id oldN newN env ps)
    | Err err = Err err
    | Just ps' with (decHsPatSecTy env ps')
      | No np = Err (TyErr ("renameExpr.renamePatTy", np))
      | Yes (Element env_e' psec') with (renameExpr lv id oldN newN env_e' e)
        | Err err = Err err
        | Just e' = Just (HsLambda {env_e=env_e'} {psec=psec'} ps' e')
renameExpr lv id oldN newN env (HsParen e) with (renameExpr lv id oldN newN env e)
  |  Err err = Err err
  |  Just e' = Just (HsParen e')

mutual 
  renameInDecl : (lv : Nat)
              -> (id : Nat)
              -> (initEnv : Env)   
              -> (oldNa : HsNameTy Variable) 
              -> (na : (EnvItem Variable))
              -> (newName : (HsNameTy Variable))
              -> (newEnv : Env)
              -> (newVars : Vect k (HsNameTy Variable) )
              -> (newSl : SameLevel newVars)
              -> (dec : HsDeclTy.HsDeclTy initEnv (Decl vars sl))
              -> ErrorOr (HsDeclTy.HsDeclTy newEnv (Decl newVars newSl))
  renameInDecl lv id initEnv oldNa na newName newEnv newVars newSl (HsFunBind {vars} (HsIdentVar lv2 id2 na2) {fnInEnv} {fnInVars} clauses) = 
    case decEq id id2 of 
      No _ => case isElemEnv newEnv (HsIdentVar lv2 id2 na2) of -- not fname
        No np => Err (TyErr ("renameInDecl.No.isElemEnv", np))
        Yes fnInEnv2' => case isElem (HsIdentVar lv2 id2 na2) newVars of 
          No np => Err (TyErr ("renameInDecl.No.isElem", np))
          Yes fnInVars2 => case (myMap (assert_total (renameInClause lv id initEnv  oldNa na newName newEnv)) clauses) of 
            Err err => Err err
            Just clauses' =>
              Just (HsFunBind {vars=newVars} (HsIdentVar lv2 id2 na2)
                   {fnInEnv=fnInEnv2'} {fnInVars=fnInVars2} clauses')
      Yes Refl => case isElemEnv newEnv newName of -- is fname
        No np => Err (TyErr ("renameInDecl.Yes.isElemEnv", np))
        Yes fnInEnv2' => case isElem newName newVars of 
          No np => Err (TyErr ("renameInDecl.No.isElem", np))
          Yes fnInVars2 => case (myMap (assert_total (renameInClause lv id initEnv  oldNa na newName newEnv)) clauses) of 
            Err err => Err err
            Just clauses' => Just (HsFunBind {vars=newVars} newName {fnInEnv=fnInEnv2'} {fnInVars=fnInVars2} clauses')
  renameInDecl lv id initEnv oldNa na newName newEnv newVars newSl (HsPatBind {sl_ws} {vars_ws} {env_e} {pInVars} {pInEnv} {envUpd} p e ws) = 
    case renamePatTySingle lv id newEnv na p of 
      Err err => Err err
      Just p' => case decHsPatTyElemVars p' newVars of 
        No np => Err (TyErr ("renameInDecl.decHsPatTyElemVars", np))
        Yes pInVars' => case decHsPatTyElemEnv newEnv p' of
          No np => Err (TyErr ("renameInDecl.decHsPatTyElemEnv", np))
          Yes pInEnv' => case updateVars newName vars_ws of
            vars_ws2 => case decSameLevel vars_ws2 of
              No np => Err (TyErr ("renameInDecl.decSameLevel", np))
              Yes sl_ws2 => case decEnvAddNewLevel newEnv vars_ws2 sl_ws2  of
                No np => Err (TyErr ("renameInDecl.decEnvAddNewLevel", np))
                Yes (Element newEnv_e envUpd') => case renameExpr lv id (getWitness (getHsIdentVarName oldNa)) (getWitness (getHsIdentVarName newName)) newEnv_e e of
                  Err err => Err err
                  Just e' => case (myMap (assert_total (renameInDecl lv id env_e oldNa na newName newEnv_e vars_ws2 sl_ws2)) ws) of
                    Err err => Err err
                    Just ws' => Just (HsPatBind {env_e=newEnv_e} p' {pInVars=pInVars'} {pInEnv=pInEnv'} {envUpd=envUpd'} e' ws')


  renameInClause : (lv : Nat)
              -> (id : Nat)
              -> (initEnv : Env)   
              -> (oldNa : HsNameTy Variable) 
              -> (na : (EnvItem Variable))
              -> (newName : (HsNameTy Variable))
              -> (newEnv : Env)
              -> (dec : HsDeclTy.HsDeclTy initEnv (FunClause (S nps)))
              -> ErrorOr (HsDeclTy.HsDeclTy newEnv (FunClause (S nps)))
  renameInClause lv id initEnv oldNa na newName newEnv (HsMatch {vars_ws} {sl_ws} {env_e} {env_ws} {envUpd} {psec} ps e ws) = case renamePatTy lv id (getWitness (getHsIdentVarName oldNa)) (getWitness (getHsIdentVarName newName)) newEnv ps of
    Err err => Err err
    Just ps' => case decHsPatSecTy newEnv ps' of 
      No np => Err (TyErr ("renameInClause.decHsPatSecTy", np))
      Yes (Element newEnv_ws psec') => case updateVars newName vars_ws of
        vars_ws2 => case decSameLevel vars_ws2 of
          No np => Err (TyErr ("renameInClause.decSameLevel", np))
          Yes sl_ws2 => case decEnvAddNewLevel newEnv_ws vars_ws2 sl_ws2 of
            No np => Err (TyErr ("renameInClause.decEnvAddNewLevel", np))
            Yes (Element env_e2 envUpd') => case renameExpr lv id (getWitness (getHsIdentVarName oldNa)) (getWitness (getHsIdentVarName newName)) env_e2 e of
              Err err => Err err
              Just e' => case (myMap (assert_total (renameInDecl lv id env_e oldNa na newName env_e2 vars_ws2 sl_ws2)) ws) of 
                Just ws' => Just (HsMatch {vars_ws=vars_ws2} {sl_ws=sl_ws2} {env_e=env_e2} {env_ws=newEnv_ws} {envUpd=envUpd'} {psec=psec'} ps' e' ws')
                Err err => Err err

renameModule : (lv,id : Nat)
            -> (oldN : HsNameTy Variable) 
            -> (newN : (HsNameTy Variable))    
            -> (mod : HsModuleTy)
            -> ErrorOr HsModuleTy
            
renameModule lv id oldN newN (HsModule {env_ds} {sl} {envRenv_ds} env vars decls) =
  case transformEnv env oldN (getWitness (hsNameTyAsEnvItem newN)) of 
    Err err => Err err
    Just env2 => 
      case updateVars newN vars of 
        vars2 => 
          case decSameLevel vars2 of 
            No np => Err (TyErr ("renameModule.decSameLevel", np))
            Yes sl2 => 
              case decEnvAddNewLevel env2 vars2 sl2 of 
                No nq => let r = Map.map getEnvItemNa (getWitness (Map.map hsNameTyAsEnvItem vars2)) in
                    Err (TyErr ("renameModule.decEnvAddNewLevel", nq, vars2, r, env2))
                Yes (Element env_ds2 envRenv_ds') => 
                  case (myMap (renameInDecl lv id env_ds oldN (getWitness (hsNameTyAsEnvItem newN)) newN env_ds2 vars2 sl2) decls) of
                    Err err => Err err
                    Just decls' => Just  (HsModule {env_ds=env_ds2} {sl=sl2} {envRenv_ds=envRenv_ds'} env2 vars2 decls')

