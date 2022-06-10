module Hs98.HsPatTy

import IdrisUtils.Utils
import IdrisUtils.Ord
import IdrisUtils.Decidability

import Hs98.HsEnv
import Hs98.HsNameTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Refined AST] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Pattern Contents] -----------------------------------------------------------------------------

||| Represents a flattened pattern definition. A pattern's children (if any) are referenced using a
||| finite set that refers to a position in the list of all flattened pattern definitions.
data HsPatDefTy : (bound : Nat) -> (env : Env) -> Type where
  HsPVar : (na : HsNameTy Variable)
        -> HsPatDefTy n env
  HsPApp : (ctr : HsNameTy Constructor)
        -> {ctrKnown : ElemEnv env ctr}
        -> (args : Vect nargs (Fin n))
        -> HsPatDefTy n env

-- [Structure and Content form a correct whole] ---------------------------------------------------

data HsPatDefTyCIds : (p : HsPatDefTy ub env)
                   -> (ncids : Nat)
                   -> (cids : Vect ncids (Fin ub))
                   -> Type where
  HsPVarCIdsNat : HsPatDefTyCIds (HsPVar na) Z []
  HsPAppCIdsNat : HsPatDefTyCIds (HsPApp {nargs} ctr args) nargs args

hsPatDefTyCIds : (p : HsPatDefTy ub env)
              -> (ncids ** Subset (Vect ncids (Fin ub)) (HsPatDefTyCIds p ncids))
hsPatDefTyCIds (HsPVar na) = (Z ** Element [] HsPVarCIdsNat)
hsPatDefTyCIds (HsPApp {nargs} ctr args) = (nargs ** Element args HsPAppCIdsNat)

lemma_HsPatDefTyCIds_injective_nids : (x : HsPatDefTy ub env)
                                   -> (nxs : Nat)
                                   -> (nys : Nat)
                                   -> (xs : Vect nxs (Fin ub))
                                   -> (ys : Vect nys (Fin ub))
                                   -> (p : HsPatDefTyCIds x nxs xs)
                                   -> (q : HsPatDefTyCIds x nys ys)
                                   -> nxs = nys
lemma_HsPatDefTyCIds_injective_nids (HsPVar _) Z Z [] [] HsPVarCIdsNat HsPVarCIdsNat = Refl
lemma_HsPatDefTyCIds_injective_nids (HsPApp {nargs} _ args) nargs nargs args args
                                    HsPAppCIdsNat HsPAppCIdsNat = Refl

lemma_HsPatDefTyCIds_injective : (x : HsPatDefTy ub env)
                              -> (n : Nat)
                              -> (xs : Vect n (Fin ub))
                              -> (ys : Vect n (Fin ub))
                              -> (p : HsPatDefTyCIds x n xs)
                              -> (q : HsPatDefTyCIds x n ys)
                              -> xs = ys
lemma_HsPatDefTyCIds_injective (HsPVar _) Z [] [] HsPVarCIdsNat HsPVarCIdsNat = Refl
lemma_HsPatDefTyCIds_injective (HsPApp {nargs} _ args) nargs args args
                               HsPAppCIdsNat HsPAppCIdsNat = Refl

||| A proof that a list of pattern nodes forms a tree of patterns.
|||
||| Assume that the root node is at the head of the list (i.e. has index `FZ`).
|||
||| Because the children of any given node are referenced by their position in the list of nodes
||| we can ensure the list of *n* nodes is a tree with *n* nodes by inspecting the the list of
||| references for all nodes, which should 1) be a set (to avoid cycles), 2) not contain reference 
||| to the root (id.), and 3) have the length *(n-1)* (to ensure that the tree has the same number
||| of nodes as those in the list of nodes).
|||
||| I wonder if it would be a good idea to verify this representation separately to make sure I've 
||| not missed any properties; i.e. can convert a proof of `(IsTree ns)` into a `RTree` 
||| representation?
data IsTree : (nodes : Vect (S n) (HsPatDefTy (S n) env)) -> Type where
  ||| 
  ||| @nodes           the list of (flattened) nodes
  ||| @cids            the concatenated list of children (if any) of each node in the list, where 
  |||                  children are represented by their indices in the list of nodes and where 
  |||                  indices in the list are represented by natural numbers
  ||| @nodesRcids_fin  relates the list of nodes and the concatenated list of children for all 
  |||                  nodes
  ||| @cids_finRcids   converts the finite set indices to natural number indices (in order to 
  |||                  simplfy proofs)
  ||| @set             a proof that the concatenated list of children contains no duplicates indices
  ||| @rootNotInCIds   a proof that the concatenated list of children does not contain the root
  ItIsTree : {nodes          : Vect (S n) (HsPatDefTy (S n) env)}
          -> {cids           : Vect n Nat}
          -> (nodesRcids_fin : ConcatQMap HsPatDefTyCIds nodes n cids_fin)
          -> (cids_finRcids  : Map FinToNat cids_fin cids)
          -> (set            : IsSet TotalOrderingNat cids)
          -> (rootNotInCIds  : All IsSucc cids)
          -> IsTree nodes

decIsTree_cids_fin : {nodes : Vect (S n) (HsPatDefTy (S n) env)}
                  -> (r : ConcatQMap HsPatDefTyCIds nodes ncids_fin cids_fin)
                  -> (neq : Not (n = ncids_fin))
                  -> Not (IsTree nodes)
decIsTree_cids_fin {cids_fin=r0} r neq (ItIsTree {cids_fin=p0} p1 p2 p3 p4) =
  case lemma_ConcatQMap_injective_len lemma_HsPatDefTyCIds_injective_nids r p1 of
    Refl =>
      case lemma_ConcatQMap_injective lemma_HsPatDefTyCIds_injective r p1 of
        Refl =>
          neq Refl

decIsTree_set : {nodes : Vect (S n) (HsPatDefTy (S n) env)}
             -> (r1 : ConcatQMap HsPatDefTyCIds nodes n cids_fin)
             -> (r2 : Map FinToNat cids_fin cids)
             -> (nset : Not (IsSet TotalOrderingNat cids))
             -> Not (IsTree nodes)
decIsTree_set {cids_fin=r0} r1 r2 nset (ItIsTree {cids_fin=p0} p1 p2 p3 p4) =
  case lemma_ConcatQMap_injective lemma_HsPatDefTyCIds_injective r1 p1 of
    Refl =>
      case lemma_Map_injective lemma_FinToNat_injective r2 p2 of
        Refl =>
          nset p3

decIsTree_root : {nodes : Vect (S n) (HsPatDefTy (S n) env)}
              -> (r1 : ConcatQMap HsPatDefTyCIds nodes n cids_fin)
              -> (r2 : Map FinToNat cids_fin cids)
              -> (contra : Not (All IsSucc cids))
              -> Not (IsTree nodes)
decIsTree_root r1 r2 contra (ItIsTree p1 p2 p3 p4) =
  case lemma_ConcatQMap_injective lemma_HsPatDefTyCIds_injective r1 p1 of
    Refl =>
      case lemma_Map_injective lemma_FinToNat_injective r2 p2 of
        Refl =>
          contra p4

decIsTree : (nodes : Vect (S n) (HsPatDefTy (S n) env)) -> Dec (IsTree nodes)
decIsTree nodes with (concatQMap hsPatDefTyCIds nodes)
  | (ncids_fin ** Element cids_fin nodesRcids_fin) =
    case decEq n ncids_fin of
      No  neq => No (decIsTree_cids_fin nodesRcids_fin neq)
      Yes Refl =>
        case map finToNat cids_fin of
          Element cids cids_finRcids =>
            case (decIsSet TotalOrderingNat cids, decAll isItSucc cids) of
              (No nset, _) =>
                No (decIsTree_set nodesRcids_fin cids_finRcids nset)
              (Yes set, No rootInCIds) =>
                No (decIsTree_root nodesRcids_fin cids_finRcids rootInCIds)
              (Yes set, Yes rootNotInCIds) =>
                Yes (ItIsTree nodesRcids_fin cids_finRcids set rootNotInCIds)

data HsPatTy : (env : Env) -> Type where
  HsPat : (defs : Vect (S n) (HsPatDefTy (S n) env)) -> {ok : IsTree defs} -> HsPatTy env

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data PatDefHasVar : HsPatDefTy ub env -> Type where
  HsPVarHasVar : PatDefHasVar (HsPVar na)

implementation Uninhabited (PatDefHasVar (HsPApp _ _)) where
  uninhabited HsPVarHasVar impossible

decPatDefHasVar : (p : HsPatDefTy ub env) -> Dec (PatDefHasVar p)
decPatDefHasVar (HsPVar na) = Yes HsPVarHasVar
decPatDefHasVar (HsPApp _ _) = No absurd

data PatDefNoVar : HsPatDefTy ub env -> Type where
  HsPAppNoVar : PatDefNoVar (HsPApp _ _)

implementation Uninhabited (PatDefNoVar (HsPVar _)) where
  uninhabited HsPAppNoVar impossible

decPatDefNoVar : (p : HsPatDefTy ub env) -> Dec (PatDefNoVar p)
decPatDefNoVar (HsPVar na) = No absurd
decPatDefNoVar (HsPApp _ _) = Yes HsPAppNoVar

lemma_PatDefHasVar_sound : (pat : HsPatDefTy ub env) -> PatDefHasVar pat -> Not (PatDefNoVar pat)
lemma_PatDefHasVar_sound (HsPVar na) HsPVarHasVar = absurd

lemma_PatDefNoVar_sound : (pat : HsPatDefTy ub env) -> PatDefNoVar pat -> Not (PatDefHasVar pat)
lemma_PatDefNoVar_sound (HsPApp _ _) HsPAppNoVar = absurd

HsPatDefTyWithVar : (HsPatDefTy ub env) -> Prop
HsPatDefTyWithVar pat =
  MkProp (PatDefHasVar pat) (PatDefNoVar pat)
         (decPatDefHasVar pat) (decPatDefNoVar pat)
         (lemma_PatDefHasVar_sound pat) (lemma_PatDefNoVar_sound pat)

decHsPatDefTyWithVar : (pat : HsPatDefTy ub env) -> Dec (HsPatDefTyWithVar pat)
decHsPatDefTyWithVar (HsPVar na) = Yes HsPVarHasVar
decHsPatDefTyWithVar (HsPApp ctr args) = No HsPAppNoVar

HsPatDefTyWithVarDec : (pat : HsPatDefTy ub env) -> Decidable (HsPatDefTyWithVar pat)
HsPatDefTyWithVarDec pat = IsDecidable (decHsPatDefTyWithVar pat)

---------------------------------------------------------------------------------------------------
-- [Relations] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HsPatDefTyVarName : (x : Subset (HsPatDefTy ub env) PatDefHasVar)
                      -> (var : HsNameTy Variable)
                      -> Type where
  HsPVarName : HsPatDefTyVarName (Element (HsPVar na) HsPVarHasVar) na

hsPatDefTyVarName : (x : Subset (HsPatDefTy ub env) PatDefHasVar)
                 -> Subset (HsNameTy Variable) (HsPatDefTyVarName x)
hsPatDefTyVarName (Element (HsPVar na) HsPVarHasVar) = Element na HsPVarName

lemma_HsPatDefTyVarName_injective : (x : Subset (HsPatDefTy ub env) PatDefHasVar)
                                 -> (y : HsNameTy Variable)
                                 -> (z : HsNameTy Variable)
                                 -> (p : HsPatDefTyVarName x y)
                                 -> (q : HsPatDefTyVarName x z)
                                 -> y = z
lemma_HsPatDefTyVarName_injective (Element (HsPVar na) HsPVarHasVar) na na HsPVarName HsPVarName =
  Refl

data HsPatTyName : (p : HsPatTy env)
                -> (nvars : Nat)
                -> (vars : Vect nvars (HsNameTy Variable))
                -> Type where
  MkHsPatTyName : (getDefsWithVars : Filter HsPatDefTyWithVar defs nvars dwvs)
               -> (dwvsRvars       : Map HsPatDefTyVarName dwvs vars)
               -> HsPatTyName (HsPat {n} defs) nvars vars

||| A decision procedure because of the call to `filter`.
hsPatTyName : (p : HsPatTy env)
           -> (nvars ** Subset (Vect nvars (HsNameTy Variable)) (HsPatTyName p nvars))
hsPatTyName (HsPat ps) with (filter HsPatDefTyWithVarDec ps)
  | (nvars ** (Element dwvs psRdwvs)) with (Map.map hsPatDefTyVarName dwvs)
    | Element vars dwvsRvars = (nvars ** Element vars (MkHsPatTyName psRdwvs dwvsRvars))

lemma_Filter_HsPatDefTyWithVarDec_injective_len : (p : Filter HsPatDefTyWithVar xs nys ys)
                                               -> (q : Filter HsPatDefTyWithVar xs nzs zs)
                                               -> nys = nzs
lemma_Filter_HsPatDefTyWithVarDec_injective_len Nil Nil = Refl
lemma_Filter_HsPatDefTyWithVarDec_injective_len (Yea p1 p2) (Yea q1 q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective_len p2 q2 of
    Refl => Refl
lemma_Filter_HsPatDefTyWithVarDec_injective_len (Yea HsPVarHasVar p2) (Nay _ q2) impossible
lemma_Filter_HsPatDefTyWithVarDec_injective_len (Nay HsPAppNoVar p2)  (Yea _ q2) impossible
lemma_Filter_HsPatDefTyWithVarDec_injective_len (Nay p1 p2) (Nay q1 q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective_len p2 q2 of
    Refl => Refl

lemma_Filter_HsPatDefTyWithVarDec_injective : (p : Filter HsPatDefTyWithVar xs n ys)
                                           -> (q : Filter HsPatDefTyWithVar xs n zs)
                                           -> ys = zs
lemma_Filter_HsPatDefTyWithVarDec_injective Nil Nil = Refl
lemma_Filter_HsPatDefTyWithVarDec_injective (Yea HsPVarHasVar p2) (Yea HsPVarHasVar q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective p2 q2 of
    Refl => Refl
lemma_Filter_HsPatDefTyWithVarDec_injective (Yea HsPVarHasVar p2) (Nay _ q2) impossible
lemma_Filter_HsPatDefTyWithVarDec_injective (Nay HsPAppNoVar p2) (Yea _ q2) impossible
lemma_Filter_HsPatDefTyWithVarDec_injective (Nay HsPAppNoVar p2) (Nay HsPAppNoVar q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective p2 q2 of
    Refl => Refl

lemma_HsPatTyName_injective_len : (pat : HsPatTy env)
                               -> (nys : Nat)
                               -> (nzs : Nat)
                               -> (ys  : Vect nys (HsNameTy Variable))
                               -> (zs  : Vect nzs (HsNameTy Variable))
                               -> (p   : HsPatTyName pat nys ys)
                               -> (q   : HsPatTyName pat nzs zs)
                               -> nys = nzs
lemma_HsPatTyName_injective_len (HsPat defs) nys nzs ys zs
                                (MkHsPatTyName p1 p2) (MkHsPatTyName q1 q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective_len p1 q1 of
    Refl => Refl

lemma_HsPatTyName_injective : (pat : HsPatTy env)
                           -> (n   : Nat)
                           -> (ys  : Vect n (HsNameTy Variable))
                           -> (zs  : Vect n (HsNameTy Variable))
                           -> (p   : HsPatTyName pat n ys)
                           -> (q   : HsPatTyName pat n zs)
                           -> ys = zs
lemma_HsPatTyName_injective (HsPat defs) n ys zs (MkHsPatTyName p1 p2) (MkHsPatTyName q1 q2) =
  case lemma_Filter_HsPatDefTyWithVarDec_injective p1 q1 of
    Refl =>
      case lemma_Map_injective lemma_HsPatDefTyVarName_injective p2 q2 of
        Refl => Refl

---------------------------------------------------------------------------------------------------
-- [Patterns and Environments] --------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that for a given pattern and list of declared variables, all variables declared in that 
||| pattern can be found in the list.
data HsPatTyElemVars : (p : HsPatTy env) -> (vars : Vect nvars (HsNameTy Variable)) -> Type where
  MkHsPatTyElemVars : (pRvars_p : HsPatTyName p nvars_p vars_p)
                   -> (pInVars  : All (\var => Elem var vars) vars_p)
                   -> HsPatTyElemVars p vars

decHsPatTyElemVars_all : (r1 : HsPatTyName p nvars_p vars_p)
                      -> (contra : Not (All (\var => Elem var vars) vars_p))
                      -> Not (HsPatTyElemVars p vars)
decHsPatTyElemVars_all {p} {nvars_p=r0} {vars_p=r1} r2 contra
                       (MkHsPatTyElemVars {nvars_p=p0} {vars_p=p1} p2 p3) =
  case lemma_HsPatTyName_injective_len p r0 p0 r1 p1 r2 p2 of
    Refl =>
      case lemma_HsPatTyName_injective p r0 r1 p1 r2 p2 of
        Refl => contra p3

decHsPatTyElemVars : (p : HsPatTy env)
                  -> (vars : Vect nvars (HsNameTy Variable))
                  -> Dec (HsPatTyElemVars p vars)
decHsPatTyElemVars p vars with (hsPatTyName p)
  | (nvars_p ** Element vars_p pRvars_p) with (decAll {p=\x => Elem x vars}
                                                      (\var => Vect.isElem var vars) vars_p)
    | No nall = No (decHsPatTyElemVars_all pRvars_p nall)
    | Yes all = Yes (MkHsPatTyElemVars pRvars_p all)

||| A proof that for a given pattern and environment, all variables declared in that pattern can
||| be found in the environment.
data HsPatTyElemEnv : (env : Env) -> (p : HsPatTy env) -> Type where
  MkHsPatTyElemEnv : (pRvars_p : HsPatTyName p nvars_p vars_p)
                  -> (pInVars  : All (ElemEnv env) vars_p)
                  -> HsPatTyElemEnv env p

decHsPatTyElemEnv_all : (r1 : HsPatTyName p nvars_p vars_p)
                     -> (contra : Not (All (ElemEnv env) vars_p))
                     -> Not (HsPatTyElemEnv env p)
decHsPatTyElemEnv_all {p} {nvars_p=r0} {vars_p=r1} r2 contra
                      (MkHsPatTyElemEnv {nvars_p=p0} {vars_p=p1} p2 p3) =
  case lemma_HsPatTyName_injective_len p r0 p0 r1 p1 r2 p2 of
    Refl =>
      case lemma_HsPatTyName_injective p r0 r1 p1 r2 p2 of
        Refl => contra p3

decHsPatTyElemEnv : (env : Env) -> (p : HsPatTy env) -> Dec (HsPatTyElemEnv env p)
decHsPatTyElemEnv env p with (hsPatTyName p)
  | (nvars_p ** Element vars_p pRvars_p) with (decAll (isElemEnv env) vars_p)
    | No nall = No (decHsPatTyElemEnv_all pRvars_p nall)
    | Yes all = Yes (MkHsPatTyElemEnv pRvars_p all)

---------------------------------------------------------------------------------------------------
-- [Abstractions over Pattern correctness and Environment update] ---------------------------------
---------------------------------------------------------------------------------------------------

||| Contains correctness proofs and environment update relations for a list of patterns.
data HsPatSecTy : (env_init : Env)
               -> (ps       : Vect (S nps) (HsPatTy env))
               -> (env_new  : Env)
               -> Type where
  |||
  ||| @vars      a list of variables declared in the list of patterns
  ||| @sameLevel a proof that the list of variables all state that they are declared in the same
  |||            scope level
  ||| @envUpdate a relation between an initial environment and that environment with the declared
  |||            variables added
  HsPatSec : (psRvars   : ConcatQMap HsPatTyName ps nvars vars)
          -> (sameLevel : SameLevel vars)
          -> (envUpdate : EnvAddNewLevel env_init vars sameLevel env_new)
          -> HsPatSecTy env_init ps env_new

decHsPatSecTy_lv : (r1 : ConcatQMap HsPatTyName ps nvars vars)
                -> (contra : Not (SameLevel vars))
                -> Not (Subset Env (HsPatSecTy env ps))
decHsPatSecTy_lv r1 contra (Element _ (HsPatSec p1 p2 p3)) =
  case lemma_ConcatQMap_injective_len lemma_HsPatTyName_injective_len r1 p1 of
    Refl =>
      case lemma_ConcatQMap_injective lemma_HsPatTyName_injective r1 p1 of
        Refl => contra p2

decHsPatSecTy_env : {ps : Vect (S nps) (HsPatTy env)}
                 -> (r1 : ConcatQMap HsPatTyName ps nvars vars)
                 -> (r2 : SameLevel vars)
                 -> (contra : Not (Subset Env (EnvAddNewLevel env vars r2)))
                 -> Not (Subset Env (HsPatSecTy env ps))
decHsPatSecTy_env r1 r2 contra (Element env' (HsPatSec p1 p2 p3)) =
  case lemma_ConcatQMap_injective_len lemma_HsPatTyName_injective_len r1 p1 of
    Refl =>
      case lemma_ConcatQMap_injective lemma_HsPatTyName_injective r1 p1 of
        Refl =>
          case lemma_SameLevel_singleton r2 p2 of
            Refl => contra (Element env' p3)

decHsPatSecTy : (env : Env)
             -> (ps : Vect (S nps) (HsPatTy env))
             -> Dec (Subset Env (HsPatSecTy env ps))
decHsPatSecTy env ps with (concatQMap hsPatTyName ps)
  | (nvars ** (Element vars psRvars)) with (decSameLevel vars)
    | No nsameLevel = No (decHsPatSecTy_lv psRvars nsameLevel)
    | Yes sameLevel with (decEnvAddNewLevel env vars sameLevel)
      | No nenvUpdate = No (decHsPatSecTy_env psRvars sameLevel nenvUpdate)
      | Yes (Element env' envUpdate) = Yes (Element env' (HsPatSec psRvars sameLevel envUpdate))

---------------------------------------------------------------------------------------------------
-- [Names in Patterns] ----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that a variable is declared in a list of (flattened) patterns.
data DecldVectHsPatDefTy : (lvl : Nat)
                        -> (id : Nat)
                        -> (v : Name Variable)
                        -> (ps : Vect nps (HsPatDefTy ub env))
                        -> Type where
  HerePVar : DecldVectHsPatDefTy lvl id na (HsPVar (HsIdentVar lvl id na) :: ps)
  TherePDefs : (there : DecldVectHsPatDefTy lvl id v ps) -> DecldVectHsPatDefTy lvl id v (p :: ps)

implementation Uninhabited (DecldVectHsPatDefTy lvl id v []) where
  uninhabited HerePVar impossible
  uninhabited TherePDefs impossible

isDecldVectHsPatDefTy : (lvl : Nat)
                     -> (id : Nat)
                     -> (v  : Name Variable)
                     -> (ps : Vect nps (HsPatDefTy ub env))
                     -> Dec (DecldVectHsPatDefTy lvl id v ps)
isDecldVectHsPatDefTy lvl id v [] = No absurd

isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lv id' na) :: ps) with (decEq lvl lv)
  isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id' na) :: ps) | Yes Refl with (decEq id id')
    isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id na) :: ps) | Yes Refl | Yes Refl with (decEq v na)
      isDecldVectHsPatDefTy lvl id na (HsPVar (HsIdentVar lvl id na) :: ps) | Yes Refl | Yes Refl | Yes Refl =
        Yes HerePVar 
      isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id na) :: ps) | Yes Refl | Yes Refl | No neq
        with (isDecldVectHsPatDefTy lvl id v ps)
          isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id na) :: ps) | Yes Refl | Yes Refl | No neq | Yes prf =
           Yes (TherePDefs prf)
          isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id na) :: ps) | Yes Refl | Yes Refl | No neq | No np =
            No (contra neq np) where
              contra : (np1 : Not (v = w))
                  -> (np2 : Not (DecldVectHsPatDefTy lvl id v ps))
                  -> Not (DecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar ld id w) :: ps))
              contra np1 np2 HerePVar = np1 Refl
              contra np1 np2 (TherePDefs p2) = np2 p2

    isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id' na) :: ps) | Yes Refl | No neq
          with (isDecldVectHsPatDefTy lvl id v ps)
            isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id' na) :: ps) | Yes Refl | No neq | Yes prf =
              Yes (TherePDefs prf)
            isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lvl id' na) :: ps) | Yes Refl | No neq | No np =
              No (contra neq np) where
                contra : (np1 : Not (i = j))
                      -> (np2 : Not (DecldVectHsPatDefTy l i v ps))
                      -> Not (DecldVectHsPatDefTy l i v (HsPVar (HsIdentVar ld j w) :: ps))
                contra np1 np2 HerePVar = np1 Refl
                contra np1 np2 (TherePDefs p2) = np2 p2

  isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lv id' na) :: ps) | No neq
                with (isDecldVectHsPatDefTy lvl id v ps)
                  isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lv id' na) :: ps) | No neq | Yes prf =
                    Yes (TherePDefs prf)
                  isDecldVectHsPatDefTy lvl id v (HsPVar (HsIdentVar lv id' na) :: ps) | No neq | No np =
                    No (contra neq np) where
                     contra : (neq : (lvl2 = lv2) -> Void)
                           -> (np : DecldVectHsPatDefTy lvl2 id2 v2 ps2 -> Void)
                           -> Not (DecldVectHsPatDefTy lvl2 id2 v2 (HsPVar (HsIdentVar lv2 id2' na2) :: ps2))
                     contra neq np HerePVar = neq Refl
                     contra np1 np2 (TherePDefs p2) = np2 p2
        
isDecldVectHsPatDefTy lvl id v (HsPApp _ _ :: ps) with (isDecldVectHsPatDefTy lvl id v ps)
  isDecldVectHsPatDefTy lvl id v (HsPApp _ _ :: ps) | Yes prf = Yes (TherePDefs prf)
  isDecldVectHsPatDefTy lvl id v (HsPApp _ _ :: ps) | No contra = No (\(TherePDefs p) => contra p)

data DecldVectHsPatTy : (lvl : Nat)
                     -> (id : Nat)
                     -> (v : Name Variable)
                     -> (ps : Vect nps (HsPatTy env))
                     -> Type where
  HerePat : (there : DecldVectHsPatDefTy lvl id v ds) -> DecldVectHsPatTy lvl id v (HsPat ds :: ps)
  TherePats : (there : DecldVectHsPatTy lvl id v ps) -> DecldVectHsPatTy lvl id v (HsPat ds :: ps)

implementation Uninhabited (DecldVectHsPatTy lvl id v []) where
  uninhabited HerePat impossible
  uninhabited TherePats impossible

isDecldVectHsPatTy : (lvl : Nat)
                  -> (id : Nat)
                  -> (v : Name Variable)
                  -> (ps : Vect nps (HsPatTy env))
                  -> Dec (DecldVectHsPatTy lvl id v ps)
isDecldVectHsPatTy lvl id v [] = No absurd

isDecldVectHsPatTy lvl id v (HsPat ds :: ps) with (isDecldVectHsPatDefTy lvl id v ds)
  isDecldVectHsPatTy lvl id v (HsPat ds :: ps) | Yes prf = Yes (HerePat prf)
  isDecldVectHsPatTy lvl id v (HsPat ds :: ps) | No contra_ds with (isDecldVectHsPatTy lvl id v ps)
    isDecldVectHsPatTy lvl id v (HsPat ds :: ps) | No contra_ds | Yes prf = Yes (TherePats prf)
    isDecldVectHsPatTy lvl id v (HsPat ds :: ps) | No contra_ds | No contra_ps =
      No (contra contra_ds contra_ps) where
        contra : (np1 : Not (DecldVectHsPatDefTy lvl id v ds))
              -> (np2 : Not (DecldVectHsPatTy lvl id v ps))
              -> Not (DecldVectHsPatTy lvl id v (HsPat ds :: ps))
        contra np1 np2 (HerePat p1) = np1 p1
        contra np1 np2 (TherePats p2) = np2 p2
