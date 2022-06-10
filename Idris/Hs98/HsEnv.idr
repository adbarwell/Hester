module Hs98.HsEnv

import IdrisUtils.Utils
import IdrisUtils.Ord
import Hs98.HsNameTy

import public Hs98.HsEnv.HsEnvItem

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that all variable names in a list of environment items are unique.
data UniqueNames : (vars : Vect nvars (EnvItem Variable)) -> Type where
  MkUniqueNames : (varsRnas : Map EnvItemNa vars nas)
               -> (set_nas  : IsSet TotalOrderingVarName nas)
               -> UniqueNames vars

decUniqueNames_set : (r1 : Map EnvItemNa vars nas)
                  -> (contra : Not (IsSet TotalOrderingVarName nas))
                  -> Not (UniqueNames vars)
decUniqueNames_set r1 contra (MkUniqueNames p1 p2) =
  case lemma_Map_injective lemma_EnvItemNa_injective r1 p1 of
    Refl => contra p2

decUniqueNames : (vars : Vect nvars (EnvItem Variable)) -> Dec (UniqueNames vars)
decUniqueNames vars with (Map.map getEnvItemNa vars)
  | Element nas varsRnas with (decIsSet TotalOrderingVarName nas)
    | No nset = No (decUniqueNames_set varsRnas nset)
    | Yes set = Yes (MkUniqueNames varsRnas set)

lemma_UniqueNames_singleton : {xs  : Vect nvars (EnvItem Variable)}
                           -> (p,q : UniqueNames xs)
                           -> p = q
lemma_UniqueNames_singleton (MkUniqueNames p1 p2) (MkUniqueNames q1 q2) =
  case lemma_Map_injective lemma_EnvItemNa_injective p1 q1 of
    Refl =>
      case lemma_Map_singleton lemma_EnvItemNa_singleton p1 q1 of
        Refl =>
          case lemma_IsSet_singleton p2 q2 of
            Refl => Refl

||| Groups together variables that are declared in the same scope. For our purposes, this means
||| that the variables here were defined in the same pattern or list of patterns in the same
||| lambda or match.
|||
||| Although linearity is checked here, uniqueness of identifiers is done at the environment level.
data ScopeLevel : Type where
  |||
  ||| @lvl  the scope level identifier
  ||| @vars a list of variables
  ||| @lin  a proof that no two variable names are the same
  MkScopeLevel : (lvl  : Nat)
              -> (vars : Vect nvars (EnvItem Variable))
              -> {lin  : UniqueNames vars}
              -> ScopeLevel


absurd_3 : {vars1 : Vect n (EnvItem Variable)}
       ->  {vars2 : Vect m (EnvItem Variable)}
       ->  (neq_nvars : (n = m) -> Void)
       ->  (MkScopeLevel lvl1 vars1 = MkScopeLevel lvl1 vars2) 
       ->  Void
absurd_3 {n=m} {m=m} neq_nvars Refl = neq_nvars Refl


absurd_4 :  {vars1 : Vect n (EnvItem Variable)}
         -> {vars2 : Vect m (EnvItem Variable)}
         -> (neq_nvars : (vars1 = vars2) -> Void)
         -> (MkScopeLevel lvl1 vars1 = MkScopeLevel lvl1 vars2) 
         -> Void
absurd_4 neq_nvars Refl = neq_nvars Refl

implementation Equality.DecEq (ScopeLevel) where
  decEq (MkScopeLevel {nvars=n} lvl1 vars1 {lin = lin1})
        (MkScopeLevel {nvars=m} lvl2 vars2 {lin = lin2}) =
    case decEq lvl1 lvl2 of 
      No neq_lvl => No (\Refl => neq_lvl Refl)
      Yes Refl   => case decEq n m of
                      No neq_nvars => No (absurd_3 neq_nvars)
                      Yes Refl     => case decEq vars1 vars2 of
                                          No neq_nvars' => No (absurd_4 neq_nvars')
                                          Yes Refl      => case lemma_UniqueNames_singleton lin1 lin2 of
                                                              Refl => Yes Refl

||| Relation between a scope level and its list of variable identifiers.
data ScopeLevelIds : (sl : ScopeLevel) -> (nids : Nat) -> (ids : Vect nids Nat) -> Type where
  |||
  ||| @nvars the length of the list of variables within the scope level.
  MkScopeLevelIds : {vars     : Vect nvars (EnvItem Variable)}
                 -> (varsRids : Map EnvItemId vars ids)
                 -> ScopeLevelIds (MkScopeLevel lvl vars) nvars ids

getScopeLevelIds : (sl : ScopeLevel) -> (nids ** Subset (Vect nids Nat) (ScopeLevelIds sl nids))
getScopeLevelIds (MkScopeLevel {nvars} lvl vars) with (Map.map getEnvItemId vars)
  | Element ids varsRids = (nvars ** Element ids (MkScopeLevelIds varsRids))

lemma_ScopeLevelIds_injective_len : (xs  : ScopeLevel)
                                 -> (nys : Nat)
                                 -> (nzs : Nat)
                                 -> (ys  : Vect nys Nat)
                                 -> (zs  : Vect nzs Nat)
                                 -> (p   : ScopeLevelIds xs nys ys)
                                 -> (q   : ScopeLevelIds xs nzs zs)
                                 -> nys = nzs
lemma_ScopeLevelIds_injective_len (MkScopeLevel lvl vars) nvars nvars ys zs
                                  (MkScopeLevelIds p1) (MkScopeLevelIds q1) =
  Refl

lemma_ScopeLevelIds_injective : (xs  : ScopeLevel)
                             -> (n   : Nat)
                             -> (ys  : Vect n Nat)
                             -> (zs  : Vect n Nat)
                             -> (p   : ScopeLevelIds xs n ys)
                             -> (q   : ScopeLevelIds xs n zs)
                             -> ys = zs
lemma_ScopeLevelIds_injective (MkScopeLevel lvl vars) nvars ys zs
                              (MkScopeLevelIds p1) (MkScopeLevelIds q1) =
  case lemma_Map_injective lemma_EnvItemId_injective p1 q1 of
    Refl => Refl

lemma_ScopeLevelIds_singleton :  (xs  : ScopeLevel)
                              -> (n   : Nat)
                              -> (ys  : Vect n Nat)
                              -> (p   : ScopeLevelIds xs n ys)
                              -> (q   : ScopeLevelIds xs n ys)
                              -> p = q
lemma_ScopeLevelIds_singleton (MkScopeLevel lvl vars) nvars ys (MkScopeLevelIds p1) (MkScopeLevelIds q1) =
    case lemma_Map_singleton lemma_EnvItemId_singleton p1 q1 of
      Refl => Refl

||| Relation between a scope level and its identifier.
data ScopeLevelLv : (sl : ScopeLevel) -> (id : Nat) -> Type where
  MkScopeLevelLv : ScopeLevelLv (MkScopeLevel lvl vars) lvl

getScopeLevelLv : (sl : ScopeLevel) -> Subset Nat (ScopeLevelLv sl)
getScopeLevelLv (MkScopeLevel lvl vars) = Element lvl MkScopeLevelLv

lemma_ScopeLevelLv_injective : (x : ScopeLevel)
                            -> (y : Nat)
                            -> (z : Nat)
                            -> (p : ScopeLevelLv x y)
                            -> (q : ScopeLevelLv x z)
                            -> y = z
lemma_ScopeLevelLv_injective (MkScopeLevel lvl vars) lvl lvl MkScopeLevelLv MkScopeLevelLv =
  Refl

lemma_ScopeLevelLv_singleton : (x : ScopeLevel)
                              -> (y : Nat)
                              -> (p : ScopeLevelLv x y)
                              -> (q : ScopeLevelLv x y)
                              -> p = q
lemma_ScopeLevelLv_singleton (MkScopeLevel lvl vars) lvl  MkScopeLevelLv MkScopeLevelLv =
  Refl

||| A proof that identifiers across an environment (i.e. lists of constructors and scope levels)
||| are unique.
data UniqueIds : (ctrs : Vect nctrs (EnvItem Constructor))
              -> (lvls : Vect nlvls ScopeLevel)
              -> Type where
  |||
  ||| @cids     the list of constructor identifiers
  ||| @sids     the list of scope identifiers
  ||| @vids     the list of variable identifiers
  ||| @set_lvls a proof that all scope identifiers are unique
  ||| @set_ids  a proof that all variable and constructor identifiers are unique
  MkUniqueIds : (ctrsRcids : Map EnvItemId ctrs cids)
             -> (lvlsRsids : Map ScopeLevelLv lvls sids)
             -> (lvlsRvids : ConcatQMap ScopeLevelIds lvls nvids vids)
             -> (set_lvls  : IsSet TotalOrderingNat sids)
             -> (set_ids   : IsSet TotalOrderingNat (cids ++ vids))
             -> UniqueIds ctrs lvls


lemma_UniqueIds_singleton :  (p,q : UniqueIds xs ys) 
                          -> p = q
lemma_UniqueIds_singleton (MkUniqueIds {cids=p1} {sids=p2} {nvids=p3} {vids=p4} p5 p6 p7 p8 p9) (MkUniqueIds {cids=q1} {sids=q2} {nvids=q3} {vids=q4} q5 q6 q7 q8 q9) =
  case lemma_Map_injective lemma_EnvItemId_injective p5 q5 of
    Refl =>
      case lemma_Map_singleton lemma_EnvItemId_singleton p5 q5 of
        Refl => case lemma_Map_injective lemma_ScopeLevelLv_injective p6 q6 of
                  Refl => case lemma_Map_singleton lemma_ScopeLevelLv_singleton p6 q6 of 
                    Refl => case lemma_ConcatQMap_injective_len lemma_ScopeLevelIds_injective_len p7 q7 of
                              Refl => case lemma_ConcatQMap_injective lemma_ScopeLevelIds_injective p7 q7 of
                                        Refl => case lemma_ConcatQMap_singleton lemma_ScopeLevelIds_singleton p7 q7 of
                                                  Refl => case lemma_IsSet_singleton p8 q8 of 
                                                         Refl => case lemma_IsSet_singleton p9 q9 of
                                                                   Refl => Refl

decUniqueIds_lvls : (r1 : Map ScopeLevelLv lvls sids)
                 -> (contra : Not (IsSet TotalOrderingNat sids))
                 -> Not (UniqueIds ctrs lvls)
decUniqueIds_lvls r1 contra (MkUniqueIds p1 p2 p3 p4 p5) =
  case lemma_Map_injective lemma_ScopeLevelLv_injective r1 p2 of
    Refl => contra p4

decUniqueIds_ids : (r1 : Map EnvItemId ctrs cids)
                -> (r2 : ConcatQMap ScopeLevelIds lvls nvids vids)
                -> (contra : Not (IsSet TotalOrderingNat (cids ++ vids)))
                -> Not (UniqueIds ctrs lvls)
decUniqueIds_ids r1 r2 contra (MkUniqueIds p1 p2 p3 p4 p5) =
  case (lemma_Map_injective lemma_EnvItemId_injective r1 p1,
        lemma_ConcatQMap_injective_len lemma_ScopeLevelIds_injective_len r2 p3) of
    (Refl, Refl) =>
      case lemma_ConcatQMap_injective lemma_ScopeLevelIds_injective r2 p3 of
        Refl => contra p5

decUniqueIds : (ctrs : Vect nctrs (EnvItem Constructor))
            -> (lvls : Vect nlvls ScopeLevel)
            -> Dec (UniqueIds ctrs lvls)
decUniqueIds ctrs lvls with (Map.map getEnvItemId ctrs,
                             Map.map getScopeLevelLv lvls,
                             concatQMap getScopeLevelIds lvls)
  | (Element cids ctrsRcids,
     Element sids lvlsRsids,
     (nvids ** Element vids lvlsRvids)) with (decIsSet TotalOrderingNat sids)
    | No nset_lvls = No (decUniqueIds_lvls lvlsRsids nset_lvls)
    | Yes set_lvls with (decIsSet TotalOrderingNat (cids ++ vids))
      | No nset_ids = No (decUniqueIds_ids ctrsRcids lvlsRvids nset_ids)
      | Yes set_ids = Yes (MkUniqueIds ctrsRcids lvlsRsids lvlsRvids set_lvls set_ids)

||| An environment in order to ensure that all occurrences of variables are bound.
data Env : Type where
  ||| 
  ||| @ctrs a list of constructors
  ||| @lvls a list variables split into scope levels; names are unique within scope levels
  ||| @ok   a proof that both scope identifiers are unique, and that variable and constructor 
  |||       identifiers are unique
  MkEnv : (ctrs : Vect nctrs (EnvItem Constructor))
       -> (lvls : Vect nlvls ScopeLevel)
       -> {ok   : UniqueIds ctrs lvls}
       -> Env

---------------------------------------------------------------------------------------------------
-- [Properties and Relations] ---------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Relates a variable name and its equivalent environment item form
data HsNameTyAsEnvItem : (na : HsNameTy Variable) -> (ei : EnvItem Variable) -> Type where
  MkHsNameTyAsEnvItem : HsNameTyAsEnvItem (HsIdentVar lv id na) (MkEnvItem id na) 

hsNameTyAsEnvItem : (var : HsNameTy Variable) -> Subset (EnvItem Variable) (HsNameTyAsEnvItem var)
hsNameTyAsEnvItem (HsIdentVar lv id na) = Element (MkEnvItem id na) MkHsNameTyAsEnvItem

lemma_HsNameTyAsEnvItem_injective : (x : HsNameTy Variable)
                                 -> (y : EnvItem Variable)
                                 -> (z : EnvItem Variable)
                                 -> (p : HsNameTyAsEnvItem x y)
                                 -> (q : HsNameTyAsEnvItem x z)
                                 -> y = z
lemma_HsNameTyAsEnvItem_injective (HsIdentVar lv id na) (MkEnvItem id na) (MkEnvItem id na)
                                  MkHsNameTyAsEnvItem MkHsNameTyAsEnvItem =
  Refl

-- [DecEq] ----------------------------------------------------------------------------------------

absurd_0 :  (cNEQ : (n = m) -> Void)
         -> (MkEnv {nctrs=n} ctrs lvls = MkEnv {nctrs=m} ctrs2 lvls2) 
         -> Void
absurd_0 cNEQ Refl = cNEQ Refl

absurd_5 :  (cNEQ3 : (nn = mm) -> Void)
         -> (MkEnv {nlvls=nn} ctrs lvls = MkEnv {nlvls=mm} ctrs2 lvls2) 
         -> Void
absurd_5 cNEQ3 Refl = cNEQ3 Refl 

absurd_6 : (cNEQ5 : (lvls = lvls2) -> Void)
        -> (MkEnv ctrs lvls = MkEnv ctrs2 lvls2) 
        -> Void
absurd_6 cNEQ5 Refl = cNEQ5 Refl 

decEq : (e1 : Env) -> (e2 : Env) -> Dec (e1 = e2)
decEq (MkEnv {nctrs = n} {nlvls=nn} {ok=nnn} ctrs lvls)
      (MkEnv {nctrs = m} {nlvls=mm} {ok=mmm} ctrs2 lvls2) = 
  case decEq n m of
    No cNEQ => No (absurd_0 cNEQ)
    Yes Refl =>
      case decEq ctrs ctrs2 of
        No cNEQ2 => No (\Refl => cNEQ2 Refl) 
        Yes Refl =>
          case decEq nn mm of
            No cNEQ3 => No (absurd_5 cNEQ3)
            Yes Refl =>
              case decEq lvls lvls2 of 
                No cNEQ5 => No (absurd_6 cNEQ5)
                Yes Refl =>
                  case lemma_UniqueIds_singleton nnn mmm of
                    Refl => Yes Refl


-- [Membership] -----------------------------------------------------------------------------------

||| A proof that a variable identifier is in a list of scope levels
data ElemScopeLevel : (lvls : Vect nlvls ScopeLevel) -> (x : HsNameTy Variable) -> Type where
  ThisLevel  : (here : Elem (MkEnvItem id_var na) vars)
            -> ElemScopeLevel (MkScopeLevel id_lvl vars :: lvls) (HsIdentVar id_lvl id_var na)
  LaterLevel : (lvl_neq : NotEq {ord=TotalOrderingNat} lvl id_lvl)
            -> (there   : ElemScopeLevel lvls (HsIdentVar id_lvl id_var na))
            -> ElemScopeLevel (MkScopeLevel lvl vars :: lvls) (HsIdentVar id_lvl id_var na)

implementation Uninhabited (ElemScopeLevel [] x) where
  uninhabited ThisLevel impossible
  uninhabited LaterLevel impossible

isElemScopeLevel_here : (nhere : Not (Elem (MkEnvItem id na) vars))
                     -> ElemScopeLevel (MkScopeLevel slv vars :: lvls) (HsIdentVar slv id na)
                     -> Void
isElemScopeLevel_here nhere (ThisLevel here) = nhere here
isElemScopeLevel_here nhere (LaterLevel lvl_neq there) = lemma_NotEq_irreflexive lvl_neq

isElemScopeLevel_eq : (neq : Not (slv = lv))
                   -> (eq  : Not (NotEq {ord=TotalOrderingNat} slv lv))
                   -> ElemScopeLevel (MkScopeLevel slv vars :: lvls) (HsIdentVar lv id na)
                   -> Void
isElemScopeLevel_eq neq eq (ThisLevel here) = neq Refl
isElemScopeLevel_eq neq eq (LaterLevel lvl_neq there) = eq lvl_neq

isElemScopeLevel_there : (neq : Not (slv = lv))
                      -> (nthere : Not (ElemScopeLevel lvls (HsIdentVar lv id na)))
                      -> ElemScopeLevel (MkScopeLevel slv vars :: lvls) (HsIdentVar lv id na)
                      -> Void
isElemScopeLevel_there neq nthere (ThisLevel here) = neq Refl
isElemScopeLevel_there neq nthere (LaterLevel lvl_neq there) = nthere there

isElemScopeLevel : (lvls : Vect nlvls ScopeLevel)
                -> (x : HsNameTy Variable)
                -> Dec (ElemScopeLevel lvls x)
isElemScopeLevel [] (HsIdentVar lv id na) = No absurd
isElemScopeLevel (MkScopeLevel slv vars :: lvls) (HsIdentVar lv id na) =
  case (decEq slv lv) of
    Yes Refl =>
      case (Vect.isElem (MkEnvItem id na) vars) of
        Yes here => Yes (ThisLevel here)
        No nhere => No (isElemScopeLevel_here nhere)
    No neq_lv =>
      case (decNotEq TotalOrderingNat slv lv) of
        Yes neq =>
          case (isElemScopeLevel lvls (HsIdentVar lv id na)) of
            Yes there => Yes (LaterLevel neq there)
            No nthere => No (isElemScopeLevel_there neq_lv nthere)
        No eq_lv => No (isElemScopeLevel_eq neq_lv eq_lv)

||| Proof that a name is within an environment.
data ElemEnv : (env : Env) -> (na : HsNameTy nk) -> Type where
  HsIdentVar : (elem : ElemScopeLevel lvls (HsIdentVar lv id na))
            -> ElemEnv (MkEnv ctrs lvls) (HsIdentVar lv id na)
  HsIdentCtr : (elem : Elem (MkEnvItem id na) ctrs)
            -> ElemEnv (MkEnv ctrs lvls) (HsIdentCtr id na)

isElemEnv : (env : Env) -> (na : HsNameTy nk) -> Dec (ElemEnv env na)
isElemEnv (MkEnv ctrs lvls) (HsIdentVar lv id na)
  with (isElemScopeLevel lvls (HsIdentVar lv id na))
    | No nelem = No (\(HsIdentVar elem) => nelem elem)
    | Yes elem = Yes (HsIdentVar elem)
isElemEnv (MkEnv ctrs lvls) (HsIdentCtr id na)
  with (Vect.isElem (MkEnvItem id na) ctrs)
    | No nelem = No (\(HsIdentCtr elem) => nelem elem)
    | Yes elem = Yes (HsIdentCtr elem)

---------------------------------------------------------------------------------------------------
-- [Operations] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A relation between an environment, a list of variables declared in the same scope level, and
||| the environment with those variables added.
data EnvAddNewLevel : (env_init  : Env)
                   -> (vars      : Vect n (HsNameTy Variable))
                   -> (sameLevel : SameLevel vars)
                   -> (env_new   : Env)
                   -> Type where
  ||| Nothing to add...
  Vacuous : EnvAddNewLevel env [] sameLevel env
  |||
  ||| @ids level  identifiers
  ||| @isNewLevel proof that the level we're adding does not have the same level identifier
  ||| @envitems   vars as envitems
  ||| @lin linearity for envitems
  ||| @newok updated ok with the new scope level
  AddLevel : (lvlsRids : Map ScopeLevelLv lvls ids)
          -> (isNewLevel : NotElem TotalOrderingNat lv ids)
          -> (varsRenvitems : Map HsNameTyAsEnvItem ((HsIdentVar lv id na) :: vars) envitems)
          -> {lin : UniqueNames envitems}
          -> {newok : UniqueIds ctrs ((MkScopeLevel lv envitems {lin = lin}) :: lvls)}
          -> EnvAddNewLevel (MkEnv ctrs lvls)
                            ((HsIdentVar lv id na) :: vars)
                            sameLevel
                            (MkEnv ctrs ((MkScopeLevel lv envitems) :: lvls) {ok=newok})

decEnvAddNewLevel_notNewLvl : (r1 : Map ScopeLevelLv lvls ids)
                           -> (contra : Not (NotElem TotalOrderingNat lv ids))
                           -> Not (Subset Env (EnvAddNewLevel (MkEnv ctrs lvls)
                                                              (HsIdentVar lv id na :: vars)
                                                              sl))
decEnvAddNewLevel_notNewLvl r1 contra (Element _ (AddLevel p1 p2 p3)) =
  case lemma_Map_injective lemma_ScopeLevelLv_injective r1 p1 of
    Refl => contra p2

decEnvAddNewLevel_lin : (r1 : Map ScopeLevelLv lvls ids)
                     -> (r2 : Map HsNameTyAsEnvItem (HsIdentVar lv id na :: vars) envitems)
                     -> (contra : Not (UniqueNames envitems))
                     -> Not (Subset Env (EnvAddNewLevel (MkEnv ctrs lvls)
                                                        (HsIdentVar lv id na :: vars)
                                                        sl))
decEnvAddNewLevel_lin r1 r2 contra (Element _ (AddLevel p1 p2 p3 {lin=p4})) =
  case lemma_Map_injective lemma_ScopeLevelLv_injective r1 p1 of
    Refl =>
      case lemma_Map_injective lemma_HsNameTyAsEnvItem_injective r2 p3 of
        Refl => contra p4

decEnvAddNewLevel_newok : (r1 : Map HsNameTyAsEnvItem ((HsIdentVar lv id na) :: vars) envitems)
                       -> (r2 : UniqueNames envitems)
                       -> (contra : Not (UniqueIds ctrs (MkScopeLevel lv envitems {lin=r2} :: lvls)))
                       -> Not (Subset Env (EnvAddNewLevel (MkEnv ctrs lvls)
                                                          (HsIdentVar lv id na :: vars)
                                                          sl))
decEnvAddNewLevel_newok r1 r2 contra (Element _ (AddLevel p1 p2 p3 {lin=p4} {newok=p5})) =
  case (lemma_Map_injective lemma_HsNameTyAsEnvItem_injective r1 p3) of
    Refl =>
      case (lemma_UniqueNames_singleton r2 p4) of
        Refl => contra p5

decEnvAddNewLevel : (env  : Env)
                 -> (vars : Vect nvars (HsNameTy Variable))
                 -> (sameLevel : SameLevel vars)
                 -> Dec (Subset Env (EnvAddNewLevel env vars sameLevel))
decEnvAddNewLevel env [] sl = Yes (Element env Vacuous)
decEnvAddNewLevel (MkEnv ctrs lvls) ((HsIdentVar lv id na) :: vars) sl
  with (Map.map getScopeLevelLv lvls)
    | Element ids lvlsRids with (isNotElem TotalOrderingNat lv ids)
      | No elem = No (decEnvAddNewLevel_notNewLvl lvlsRids elem)
      | Yes isNewLevel with (Map.map hsNameTyAsEnvItem (HsIdentVar lv id na :: vars))
        | Element envitems varsRenvitems with (decUniqueNames envitems)
          | No nlin = No (decEnvAddNewLevel_lin lvlsRids varsRenvitems nlin)
          | Yes lin with (decUniqueIds ctrs (MkScopeLevel lv envitems {lin = lin} :: lvls))
            | No nnewok = No (decEnvAddNewLevel_newok varsRenvitems lin nnewok)
            | Yes newok =
                Yes (Element (MkEnv ctrs ((MkScopeLevel lv envitems {lin = lin}) :: lvls)
                                    {ok=newok})
                    (AddLevel lvlsRids isNewLevel varsRenvitems {lin=lin} {newok=newok}))
