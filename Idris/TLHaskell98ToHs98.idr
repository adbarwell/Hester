module TLHaskell98ToHs98

import IdrisUtils.Utils
import IdrisUtils.Ord

import Haskell98
import Hs98

%default total
%access public export

data HsPatDefTyIR : Type where
  HsPVar : (na : HsNameTy) -> HsPatDefTyIR
  HsPApp : (c : HsQNameTy) -> (args : List Nat) -> HsPatDefTyIR

data HsDeclKindTyIR : Type where
  FunClause : HsDeclKindTyIR
  Decl : HsDeclKindTyIR

data HsDeclTyIR : HsDeclKindTyIR -> Type where
  HsMatch : (ps : Vect (S nps) HsPatTy)
         -> (ws : Vect nws (HsDeclTyIR Decl))
         -> (e : HsExpTy)
         -> HsDeclTyIR FunClause
  HsFunBind : (fname : HsNameTy)
           -> (cls : Vect (S ncls) (HsDeclTyIR FunClause))
           -> HsDeclTyIR Decl
  HsPatBind : (p : HsPatTy)
           -> (ws : Vect nws (HsDeclTyIR Decl))
           -> (e : HsExpTy)
           -> HsDeclTyIR Decl

---------------------------------------------------------------------------------------------------
-- [Error] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Error : Type where
  TLHsIdent : String -> List (k ** (Nat, Nat, Name k, String)) -> Error
  TLHsSymbol : String -> String -> List (k ** (Nat, Nat, Name k, String)) -> Error
  TLHsPatDefTy : Error -> Nat -> HsPatDefTyIR -> Error
  TLHsPatDefTyList : Error -> Nat -> Vect n HsPatDefTyIR -> Error
  TLHsPatTy : Error -> Haskell98.HsPatTy -> Error
  TLHsPatTyList : Error -> List Haskell98.HsPatTy -> Error
  TLHsPatTyVect : Error -> Vect nps Haskell98.HsPatTy -> Error
  TLHsExpTy : Error -> Haskell98.HsExpTy -> Env -> Error
  TLHsUnGuardedAlt : Error -> HsGuardedAltsTy -> Error
  TLHsMatchTyIR : Error -> Haskell98.HsMatchTy -> Error
  TLHsMatchTyIRList : Error -> List Haskell98.HsMatchTy -> Error
  TLHsMatchTy : Error -> HsDeclTyIR FunClause -> Error
  TLHsDeclTyIR : Error -> Haskell98.HsDeclTy -> Error
  TLHsDeclTyIRList : Error -> List Haskell98.HsDeclTy -> Error
  TLHsDeclTy : Error -> HsDeclTyIR Decl -> Error
  TLHsDeclTyList : Error -> Vect nds (HsDeclTyIR Decl) -> Error
  TLHsModuleTy : Error -> Error
  StdErr : String -> Error
  TyErr : (c : Type ** c) -> Error

liftErrors : Vect n (Either Error c) -> Either (List Error) (Vect n c)
liftErrors [] = Right []
liftErrors (Left err :: xs) with (liftErrors xs)
  | Left errs = Left (err :: errs)
  | Right xs98 = Left [err]
liftErrors (Right x :: xs) with (liftErrors xs)
  | Left errs = Left errs
  | Right xs98 = Right (x :: xs98)

---------------------------------------------------------------------------------------------------
-- [Symbol Conversion] ----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

convertSymbol : String -> Maybe String
convertSymbol s = Nothing

---------------------------------------------------------------------------------------------------
-- [Lookup] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

strictLookUp : (nameMap : List (k ** (Nat, Nat, Name k, String)))
            -> (var : String)
            -> Maybe (k ** (Nat, Nat, Name k))
strictLookUp [] var = Nothing
strictLookUp ((k ** (lv,id,na,na_str)) :: rest) var =
  case decEq var na_str of
    No _ => strictLookUp rest var
    Yes Refl => Just (k ** (lv, id, na))

---------------------------------------------------------------------------------------------------
-- [Update] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

updateNameMap : (nameMap : List (k ** (Nat, Nat, Name k, String)))
             -> (defs    : Vect n (HsPatDefTy (S m) env))
             -> (defs_ir : Vect n HsPatDefTyIR)
             -> List (k ** (Nat, Nat, Name k, String))
updateNameMap nameMap [] [] = nameMap
updateNameMap nameMap (HsPVar (HsIdentVar lv id na) :: defs) (HsPVar (HsIdent na_str) :: defs_ir) =
  (Variable ** (lv,id,na,na_str)) :: updateNameMap nameMap defs defs_ir
updateNameMap nameMap (HsPVar (HsIdentVar lv id na) :: defs) (HsPVar (HsSymbol na_str) :: defs_ir) =
  (Variable ** (lv,id,na,na_str)) :: updateNameMap nameMap defs defs_ir
updateNameMap nameMap (HsPApp _ _ :: defs) (def_ir :: defs_ir) =
  updateNameMap nameMap defs defs_ir

-- This case should not occur at the point at which we are calling updateNameMap in HsExpTy.
-- Taking the simple route and just ignoring it instead of erroring out; can change later if need
-- be.
updateNameMap nameMap (HsPVar _ :: defs) (HsPApp _ _ :: defs_ir) =
  updateNameMap nameMap defs defs_ir

---------------------------------------------------------------------------------------------------
-- [HsNameTy] -------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

tlHsNameTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
          -> Haskell98.HsNameTy
          -> Either Error (k ** HsNameTy k)
tlHsNameTy nameMap (HsIdent v) with (strictLookUp nameMap v)
  | Nothing = Left (TLHsIdent v nameMap)
  | Just (Variable ** (lv,id,na)) = Right (Variable ** (HsIdentVar lv id na))
  | Just (Constructor ** (lv,id,na)) = Right (Constructor ** (HsIdentCtr id na))
tlHsNameTy nameMap (HsSymbol s) with (convertSymbol s)
  | Nothing = Left (StdErr ("[AddMe] Unknown symbol: " ++ s))
  | Just v with (strictLookUp nameMap v)
    | Nothing = Left (TLHsSymbol s v nameMap)
    | Just (Variable ** (lv,id,na)) = Right (Variable ** (HsIdentVar lv id na))
    | Just (Constructor ** (lv,id,na)) = Right (Constructor ** (HsIdentCtr id na))

||| Called by patterns; it will add the HsNameTy to nameMap.
tlHsNameTyNew : (lv : Nat)
             -> (id : Nat)
             -> Haskell98.HsNameTy
             -> Either Error (String, (k ** HsNameTy k))
tlHsNameTyNew lv id (HsIdent na_string) with (fromString na_string)
  | Nothing = Left (StdErr "Invalid name.")
  | Just na_str with (strAsVariable na_str)
    | Yes na = Right (na_string, (Variable ** HsIdentVar lv id (getWitness na)))
    | No nvar with (strAsConstructor na_str)
      | Yes na = Right (na_string, (Constructor ** HsIdentCtr id (getWitness na)))
      | No nctr = Left (StdErr "Neither valid Variable nor Constructor.")
tlHsNameTyNew lv id (HsSymbol s_string) with (convertSymbol s_string)
  | Nothing = Left (StdErr ("[AddMe] Unknown symbol: " ++ s_string))
  | Just na_string = assert_total (tlHsNameTyNew lv id (HsIdent na_string))

{-
with (tlHsNameTy nameMap na)
  | Left err with (fromString na_str)
    | Nothing = Left (StdErr "Invalid name.")
    | Just str with (strAsVariable str)
      | No nvar with (strAsConstructor str)
        | No nctr = Left (StdErr "Name is neither valid Variable nor Constructor.")
        | Yes na = 
      | Yes var = ?
  | Right (k ** na98) = ?holeShadow
-}

tlHsSpecialConTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                -> Haskell98.HsSpecialConTy
                -> Either Error (k ** HsNameTy k)
tlHsSpecialConTy nameMap HsCons with (strictLookUp nameMap "Cons")
  | Nothing = Left (StdErr "Cons not in Environment")
  | Just (Variable ** (lv,id,na)) = Left (StdErr "Cons is not a Variable")
  | Just (Constructor ** (lv,id,na)) = Right (Constructor ** HsIdentCtr id na)

tlHsQNameTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
           -> Haskell98.HsQNameTy
           -> Either Error (k ** HsNameTy k)
tlHsQNameTy nameMap (UnQual na) = tlHsNameTy nameMap na
tlHsQNameTy nameMap (Special sp) = tlHsSpecialConTy nameMap sp

tlHsQOpTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
         -> Haskell98.HsQOpTy
         -> Either Error (k ** HsNameTy k)
tlHsQOpTy nameMap (HsQVarOp qna) = tlHsQNameTy nameMap qna

---------------------------------------------------------------------------------------------------
-- [HsPatTy] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [HsPatTy to IR forms] --------------------------------------------------------------------------

partial
tlHsPatTyDefIR : (idx : Nat) -> Haskell98.HsPatTy -> Maybe (Nat, (ub ** Vect ub HsPatDefTyIR))
tlHsPatTyDefIR idx (HsPVar na) = Just (S idx, (S Z ** [HsPVar na]))
tlHsPatTyDefIR idx (HsPApp c ps) =
  do
    (idx', ids, (n ** ps')) <- foldl step (Just (S idx, [], (Z ** []))) ps
    Just (idx', (S n ** (HsPApp c ids) :: ps'))
  where
    partial
    step : Maybe (Nat, List Nat, (n ** Vect n HsPatDefTyIR))
        -> Haskell98.HsPatTy
        -> Maybe (Nat, List Nat, (n ** Vect n HsPatDefTyIR))
    step Nothing p = Nothing
    step (Just (idx'', ids', (n ** ps''))) p = do
      (idx''', (m ** p')) <- tlHsPatTyDefIR idx'' p
      Just (idx''', ids' ++ [idx''], (n + m ** ps'' ++ p'))
tlHsPatTyDefIR idx (HsPParen p) = tlHsPatTyDefIR idx p

tlHsPatTyDefIR idx (HsPList []) = Just (idx, (S Z ** [HsPApp (UnQual (HsIdent "Nil")) []]))
tlHsPatTyDefIR idx (HsPList (p :: ps)) = Nothing
  -- let (idx', (n ** p')) = tlHsPatTyDefIR idx p
  --     (idx'', (m ** ps')) = tlHsPatTyDefIR idx (HsPList ps)
  -- in (idx'', (S n + m ** ))
tlHsPatTyDefIR idx (HsPInfixApp p1 op p2) = tlHsPatTyDefIR idx (HsPApp op [p1,p2])

-- [IR to Hs98.HsPatTy] ---------------------------------------------------------------------------

tlArgList : (ub : Nat) -> (args : List Nat) -> Maybe (nargs ** (Vect nargs (Fin ub)))
tlArgList ub args =
  map (\xs => (length xs ** fromList xs)) (traverse (\nat => natToFin nat ub) args)

tlHsPatDefTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
            -> (env : Env)
            -> (lv : Nat)
            -> (id : Nat)
            -> (ub : Nat)
            -> HsPatDefTyIR
            -> Either Error (Maybe String, HsPatDefTy ub env)
tlHsPatDefTy nameMap env lv id Z p = Left (StdErr "Upper bound cannot be zero.")
tlHsPatDefTy nameMap env lv id (S ub) (HsPVar na) with (tlHsNameTyNew lv id na)
  | Left err = Left (TLHsPatDefTy err (S ub) (HsPVar na))
  | Right (na_str, (Variable ** na98)) = Right (Just na_str, HsPVar na98)
  | Right (na_str, (Constructor ** na98)) =
    Left (TLHsPatDefTy (StdErr "Expecting Variable not Constructor.") (S ub) (HsPVar na))
tlHsPatDefTy nameMap env lv id (S ub) (HsPApp c args) with (tlHsQNameTy nameMap c)
  | Left err = Left (TLHsPatDefTy err (S ub) (HsPApp c args))
  | Right (Variable ** c98) =
    Left (TLHsPatDefTy (StdErr "Expecting Constructor not Variable.") (S ub) (HsPApp c args))
  | Right (Constructor ** c98) =
    case (isElemEnv env c98) of
      No nctrKnown => Left (TLHsPatDefTy (StdErr "Unknown constructor.") (S ub) (HsPApp c args))
      Yes ctrKnown =>
        case tlArgList (S ub) args of
          Nothing =>
            Left (TLHsPatDefTy (StdErr "Error converting args from Nat to Fin (S ub)")
                               (S ub) (HsPApp c args))
          Just (nargs98 ** args98) =>
            Right (Nothing, HsPApp c98 {ctrKnown = ctrKnown} args98)

tlHsPatDefTyKnown : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                 -> (env : Env)
                 -> (ub : Nat)
                 -> HsPatDefTyIR
                 -> Either Error (HsPatDefTy ub env)
tlHsPatDefTyKnown nameMap env Z p = Left (StdErr "Upper bound cannot be zero.")
tlHsPatDefTyKnown nameMap env (S ub) (HsPVar na) with (tlHsNameTy nameMap na)
  | Left err = Left (TLHsPatDefTy err (S ub) (HsPVar na))
  | Right (Variable ** na98) = Right (HsPVar na98)
  | Right (Constructor ** na98) =
    Left (TLHsPatDefTy (StdErr "Expecting Variable not Constructor.") (S ub) (HsPVar na))
tlHsPatDefTyKnown nameMap env (S ub) (HsPApp c args) with (tlHsQNameTy nameMap c)
  | Left err = Left (TLHsPatDefTy err (S ub) (HsPApp c args))
  | Right (Variable ** c98) =
    Left (TLHsPatDefTy (StdErr "Expecting Constructor not Variable.") (S ub) (HsPApp c args))
  | Right (Constructor ** c98) =
    case (isElemEnv env c98) of
      No nctrKnown => Left (TLHsPatDefTy (StdErr "Unknown constructor.") (S ub) (HsPApp c args))
      Yes ctrKnown =>
        case tlArgList (S ub) args of
          Nothing =>
            Left (TLHsPatDefTy (StdErr "Error converting args from Nat to Fin (S ub)")
                               (S ub) (HsPApp c args))
          Just (nargs98 ** args98) =>
            Right (HsPApp c98 {ctrKnown = ctrKnown} args98)

tlHsPatDefTyList : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                -> (env     : Env)
                -> (lv      : Nat)
                -> (id      : Nat)
                -> (ub      : Nat)
                -> (ds_ir   : Vect n HsPatDefTyIR)
                -> Either Error (Nat,
                                 List (k ** (Nat, Nat, Name k, String)),
                                 Vect n (HsPatDefTy ub env))
tlHsPatDefTyList nameMap env lv id ub [] = Right (id, nameMap, [])
tlHsPatDefTyList nameMap env lv id ub (HsPVar na :: ds_ir)
  with (tlHsPatDefTy nameMap env lv id ub (HsPVar na))
    | Left err =
      Left (TLHsPatDefTyList err ub (HsPVar na :: ds_ir))
    | Right (Nothing, HsPVar na98) =
      Left (TLHsPatDefTyList (StdErr "No name returned.") ub (HsPVar na :: ds_ir))
    | Right (Just na_str, HsPVar na98) with (tlHsPatDefTyList nameMap env lv (S id) ub ds_ir)
      | Left err = Left (TLHsPatDefTyList err ub (HsPVar na :: ds_ir))
      | Right (id', nameMap', defs) =
        Right (id',
               (Variable
                ** (lv, id, Subset.getWitness (getHsIdentVarName na98), na_str)) :: nameMap',
               (HsPVar na98) :: defs)
    | Right (_, HsPApp _ _) =
      Left (TLHsPatDefTyList (StdErr "Unexpected HsPApp.") ub (HsPVar na :: ds_ir))
tlHsPatDefTyList nameMap env lv id ub (HsPApp c args :: ds_ir)
  with (tlHsPatDefTy nameMap env lv id ub (HsPApp c args))
    | Left err =
      Left (TLHsPatDefTyList err ub (HsPApp c args :: ds_ir))
    | Right (_, HsPVar _) =
      Left (TLHsPatDefTyList (StdErr "Unexpected HsPVar.") ub (HsPApp c args :: ds_ir))
    | Right (_, HsPApp c98 {ctrKnown} args98) with (tlHsPatDefTyList nameMap env lv id ub ds_ir)
      | Left err =
        Left (TLHsPatDefTyList err ub (HsPApp c args :: ds_ir))
      | Right (id', nameMap', defs) =
        Right (id', nameMap', (HsPApp c98 {ctrKnown = ctrKnown} args98) :: defs)

tlHsPatDefTyListKnown : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                     -> (env : Env)
                     -> (ub  : Nat)
                     -> (ds_ir : Vect n HsPatDefTyIR)
                     -> Either Error (Vect n (HsPatDefTy ub env))
tlHsPatDefTyListKnown nameMap env ub [] = Right []
tlHsPatDefTyListKnown nameMap env ub (HsPVar na :: ds_ir)
  with (tlHsPatDefTyKnown nameMap env ub (HsPVar na))
    | Left err =
      Left (TLHsPatDefTyList err ub (HsPVar na :: ds_ir))
    | Right (HsPVar na98) with (tlHsPatDefTyListKnown nameMap env ub ds_ir)
      | Left err = Left (TLHsPatDefTyList err ub (HsPVar na :: ds_ir))
      | Right defs = Right (HsPVar na98 :: defs)
    | Right (HsPApp _ _) =
      Left (TLHsPatDefTyList (StdErr "Unexpected HsPApp.") ub (HsPVar na :: ds_ir))
tlHsPatDefTyListKnown nameMap env ub (HsPApp c args :: ds_ir)
  with (tlHsPatDefTyKnown nameMap env ub (HsPApp c args))
    | Left err =
      Left (TLHsPatDefTyList err ub (HsPApp c args :: ds_ir))
    | Right (HsPVar _) =
      Left (TLHsPatDefTyList (StdErr "Unexpected HsPVar.") ub (HsPApp c args :: ds_ir))
    | Right (HsPApp c98 {ctrKnown} args98) with (tlHsPatDefTyListKnown nameMap env ub ds_ir)
      | Left err = Left (TLHsPatDefTyList err ub (HsPApp c args :: ds_ir))
      | Right defs = Right (HsPApp c98 {ctrKnown = ctrKnown} args98 :: defs)

-- [All Together Now] -----------------------------------------------------------------------------

partial
tlHsPatTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
         -> (env : Env)
         -> (lv  : Nat)
         -> (id  : Nat)
         -> Haskell98.HsPatTy
         -> Either Error (Nat, List (k ** (Nat, Nat, Name k, String)), HsPatTy env)
tlHsPatTy nameMap env lv id p with (tlHsPatTyDefIR Z p)
  | Nothing = Left (StdErr "Unsupported pattern type.")
  | Just (_, (Z ** [])) = Left (TLHsPatTy (StdErr "Empty list of pattern definitions.") p)
  | Just (_, (S ub ** ds_ir)) with (tlHsPatDefTyList nameMap env lv id (S ub) ds_ir)
    | Left err = Left (TLHsPatTy err p)
    | Right (id', nameMap', defs) with (decIsTree defs)
      | No nok = Left (TLHsPatTy (StdErr "Patterns are not a tree.") p)
      | Yes ok = Right (id', nameMap', HsPat defs {ok=ok})

partial
tlHsPatTyKnown : (nameMap : List (k ** (Nat, Nat, Name k, String)))
              -> (env : Env)
              -> Haskell98.HsPatTy
              -> Either Error (HsPatTy env)
tlHsPatTyKnown nameMap env p with (tlHsPatTyDefIR Z p)
  | Nothing = Left (StdErr "Unsupported pattern type.")
  | Just (_, (Z ** [])) = Left (TLHsPatTy (StdErr "Empty list of pattern definitions.") p)
  | Just (_, (S ub ** ds_ir)) with (tlHsPatDefTyListKnown nameMap env (S ub) ds_ir)
    | Left err = Left (TLHsPatTy err p)
    | Right defs with (decIsTree defs)
      | No _ = Left (TLHsPatTy (StdErr "Patterns are not a tree.") p)
      | Yes ok = Right (HsPat defs {ok=ok})

{-
    case decEq ub nds_ir of
      No _ => Left (TLHsPatTy (StdErr "Pat Defns upper bounds disagree.") p)
      Yes Refl =>
        case liftErrors (map (step nameMap env ub) (zip (idsUpTo id ds_ir) ds_ir)) of
          Left (err :: errs) => Left (TLHsPatTy (last (err :: errs)) p)
          Right defs => case ub of
            Z => Left (TLHsPatTy (StdErr "(ub = Z); should be impossible at this point.") p)
            S n => case decIsTree defs of
              No c =>
                Left (TLHsPatTy (StdErr "Patterns are not a tree.") p)
              Yes ok =>
                Right (ub, updateNameMap nameMap defs ds_ir, HsPat defs ok)
-}

-- [List of Patterns] -----------------------------------------------------------------------------

partial
tlHsPatTyList : (nameMap : List (k ** (Nat, Nat, Name k, String)))
             -> (env : Env)
             -> (lv  : Nat)
             -> (id  : Nat)
             -> List Haskell98.HsPatTy
             -> Either Error (Nat,
                              List (k ** (Nat, Nat, Name k, String)),
                              (nps ** Vect nps (HsPatTy env)))
tlHsPatTyList nameMap env lv id [] = Right (id, nameMap, (Z ** []))
tlHsPatTyList nameMap env lv id (p :: ps) with (tlHsPatTy nameMap env lv id p)
  | Left err = Left (TLHsPatTyList err (p :: ps))
  | Right (id', nameMap', p98) with (tlHsPatTyList nameMap' env lv id' ps)
    | Left err = Left (TLHsPatTyList err (p :: ps))
    | Right (id'', nameMap'', (nps ** ps98)) = Right (id'', nameMap'', (S nps ** p98 :: ps98))

partial
tlHsPatTyVect : (nameMap : List (k ** (Nat, Nat, Name k, String)))
             -> (env : Env)
             -> (lv  : Nat)
             -> (id  : Nat)
             -> Vect nps Haskell98.HsPatTy
             -> Either Error (Nat,
                              List (k ** (Nat, Nat, Name k, String)),
                              Vect nps (HsPatTy env))
tlHsPatTyVect nameMap env lv id [] = Right (id, nameMap, [])
tlHsPatTyVect nameMap env lv id (p :: ps) with (tlHsPatTy nameMap env lv id p)
  | Left err = Left (TLHsPatTyVect err (p :: ps))
  | Right (id', nameMap', p98) with (tlHsPatTyVect nameMap' env lv id' ps)
    | Left err = Left (TLHsPatTyVect err (p :: ps))
    | Right (id'', nameMap'', ps98) = Right (id'', nameMap'', (p98 :: ps98))

-- [QuickTest] ------------------------------------------------------------------------------------

{-
tlCtrsEnv : List String -> Maybe (n ** Vect n (EnvItem Constructor))
tlCtrsEnv = tlCtrsEnv' Z where
  tlCtrsEnv' : Nat -> List String -> Maybe (n ** Vect n (EnvItem Constructor))
  tlCtrsEnv' id [] = pure (Z ** [])
  tlCtrsEnv' id (x :: xs) = do
    (n ** xs98) <- tlCtrsEnv' (S id) xs
    str <- fromString x
    case (strAsConstructor str) of
      No _ => Nothing
      Yes x98 => pure (S n ** MkEnvItem id (Subset.getWitness x98) :: xs98)

testCtrsStr : List String
testCtrsStr = ["True", "C1", "C2", "C3"]

testCtrsEnv : Maybe Env
testCtrsEnv = do
  (nctrs ** ctrs) <- tlCtrsEnv testCtrsStr
  pure (MkEnv ctrs [])

tlPatsVars : Nat -> List String -> Maybe (List (k ** (Nat, Nat, Name k, String)))
tlPatsVars id [] = pure []
tlPatsVars id (x :: xs) = do
  xs98 <- tlPatsVars (S id) xs
  str <- fromString x
  case (strAsVariable str) of
    No _ => Nothing
    Yes x98 => pure ((Variable ** (Z, id, getWitness x98, x)) :: xs98)

testCtrsNameMap : Maybe (List (k ** (Nat, Nat, Name k, String)))
testCtrsNameMap = do
  (nctrs ** ctrs) <- tlCtrsEnv testCtrsStr
  let ctrs =
    (map (\(MkEnvItem id na, s) => (Constructor ** (Z, id, na, s))) (zip (toList ctrs) testCtrsStr))
  pure (ctrs)

testVarsNameMap : Maybe (List (k ** (Nat, Nat, Name k, String)))
testVarsNameMap = tlPatsVars 4 ["x","y","z"]

||| f (C1 x y (C2 True (C3 z))) = 42
testPat : List Haskell98.HsPatTy
testPat = [HsPParen (HsPApp (UnQual (HsIdent "C1"))
                            [HsPVar (HsIdent "x"),
                             HsPVar (HsIdent "y"),
                             HsPParen (HsPApp (UnQual (HsIdent "C2"))
                                              [HsPApp (UnQual (HsIdent "True")) [],
                                               HsPParen (HsPApp (UnQual (HsIdent "C3"))
                                                                [HsPVar (HsIdent "z")])])])]

testPat98 : Maybe (Either Error (env ** HsPatTy env))
testPat98 = do
  nameMapCtrs <- testCtrsNameMap
  nameMapVars <- testVarsNameMap
  env <- testCtrsEnv
  case (tlHsPatTy (nameMapCtrs ++ nameMapVars) env Z (head testPat)) of
    Left err => Just (Left err)
    Right p98 => Just (Right (env ** p98))
-}

---------------------------------------------------------------------------------------------------
-- [HsLiteralTy] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

tlHsLiteralTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
             -> Haskell98.HsLiteralTy
             -> Either Error HsExpTy.HsLiteralTy
tlHsLiteralTy nameMap (HsInt int) = Right (HsInt int)

---------------------------------------------------------------------------------------------------
-- [HsExpTy] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

partial -- thanks to patterns
tlHsExpTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
         -> (env : Env)
         -> (lv  : Nat)
         -> (id  : Nat)
         -> Haskell98.HsExpTy
         -> Either Error (HsExpTy env)
tlHsExpTy nameMap env lv id (HsVar qna) with (tlHsQNameTy nameMap qna)
  | Left err = Left (TLHsExpTy err (HsVar qna) env)
  | Right (Constructor ** na98) =
    Left (TLHsExpTy (StdErr "Expecting Variable not Constructor") (HsVar qna) env)
  | Right (Variable ** na98) with (isElemEnv env na98)
    | No nelem = Left (TLHsExpTy (StdErr "Variable not in environment.") (HsVar qna) env)
    | Yes elem = Right (HsVar na98 {ok=elem})
tlHsExpTy nameMap env lv id (HsLit lit) with (tlHsLiteralTy nameMap lit)
  | Left err = Left (TLHsExpTy err (HsLit lit) env)
  | Right lit98 = Right (HsLit lit98)
tlHsExpTy nameMap env lv id (HsInfixApp l op r) with (tlHsExpTy nameMap env lv id l,
                                                      tlHsExpTy nameMap env lv id r)
  | (Left err, _) = Left (TLHsExpTy err (HsInfixApp l op r) env)
  | (_, Left err) = Left (TLHsExpTy err (HsInfixApp l op r) env)
  | (Right l98, Right r98) with (tlHsQOpTy nameMap op)
    | Left err = Left (TLHsExpTy err (HsInfixApp l op r) env)
    | Right (Variable ** op98) with (isElemEnv env op98)
      | No nelem = Left (TLHsExpTy (StdErr "Op not in environment.") (HsInfixApp l op r) env)
      | Yes elem = Right (HsApp (HsApp (HsVar op98 {ok=elem}) l98) r98)
    | Right (Constructor ** op98) =
      Left (TLHsExpTy (StdErr "Op is a constructor.") (HsInfixApp l op r) env)
tlHsExpTy nameMap env lv id (HsApp f e) with (tlHsExpTy nameMap env lv id f,
                                              tlHsExpTy nameMap env lv id e)
  | (Left err, _) = Left (TLHsExpTy err (HsApp f e) env)
  | (_, Left err) = Left (TLHsExpTy err (HsApp f e) env)
  | (Right f98, Right e98) = Right (HsApp f98 e98)
tlHsExpTy nameMap env lv id (HsLambda loc ps e) with (tlHsPatTyList nameMap env lv id ps)
  | Left err =
    Left (TLHsExpTy err (HsLambda loc ps e) env)
  | Right (id', nameMap', (Z ** [])) =
    Left (TLHsExpTy (StdErr "No patterns.") (HsLambda loc ps e) env)
  | Right (id', nameMap', (S nps ** ps98)) with (decHsPatSecTy env ps98)
    | No npsec = Left (TLHsExpTy (StdErr "Error constructing PatSec.") (HsLambda loc ps e) env)
    | Yes (Element env' psec) with (tlHsExpTy nameMap' env' (S lv) id' e)
      | Left err = Left (TLHsExpTy err (HsLambda loc ps e) env)
      | Right e98 = Right (HsLambda ps98 {psec=psec} e98)
tlHsExpTy nameMap env lv id (HsCase e alts) =
  Left (TLHsExpTy (StdErr "Not yet supported. Please expand case expressions into their own functions.") (HsCase e alts) env)
tlHsExpTy nameMap env lv id (HsParen e) with (tlHsExpTy nameMap env lv id e)
  | Left err = Left (TLHsExpTy err (HsParen e) env)
  | Right e98 = Right (HsParen e98)


---------------------------------------------------------------------------------------------------
-- [Hs(Guarded)Alt] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{-
tlHsGuardedAltsTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                 -> (env : Env)
                 -> Haskell98.HsGuardedAltsTy
                 -> Either Error (HsExpTy env)
tlHsGuardedAltsTy nameMap env (HsUnGuardedAlt exp) with (tlHsExpTy nameMap env exp)
  | Left err = Left (TLHsUnGuardedAlt err (HsUnGuardedAlt exp))
  | Right exp98 = Right exp98
-}

---------------------------------------------------------------------------------------------------
-- [HsMatchTy] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{-
  Scope levels for function clauses:

  fname     -> pattern names -> where clauses -> RHS
  pred (lv) -> lv            -> (S lv)        -> (S (S lv))
-}

mutual
  tlHsMatchTyIR : (fn : HsNameTy) -> HsMatchTy -> Either Error (HsDeclTyIR FunClause)
  tlHsMatchTyIR fn (HsMatch l fname [] rhs ws) =
    Left (TLHsMatchTyIR (StdErr "Clause must have at least one pattern.")
                        (HsMatch l fname [] rhs ws))
  tlHsMatchTyIR fn (HsMatch l fname (p :: ps) (HsUnGuardedRhs e) ws) with (decEq fname fn)
    tlHsMatchTyIR fn (HsMatch l fname (p :: ps) (HsUnGuardedRhs e) ws) | No _ =
      Left (TLHsMatchTyIR (StdErr "Name of match is not the same as name given")
                          (HsMatch l fname (p :: ps) (HsUnGuardedRhs e) ws))
    tlHsMatchTyIR fn (HsMatch l fn (p :: ps) (HsUnGuardedRhs e) ws) | Yes Refl =
      case tlHsDeclTyIRList ws of
        Left err => Left (TLHsMatchTyIR err (HsMatch l fn (p :: ps) (HsUnGuardedRhs e) ws))
        Right (nws ** wsIR) => Right (HsMatch (p :: fromList ps) wsIR e)

  tlHsMatchTyIRList : (fn : HsNameTy)
                  -> List HsMatchTy
                  -> Either Error (nms ** Vect nms (HsDeclTyIR FunClause))
  tlHsMatchTyIRList fn [] = Right (Z ** [])
  tlHsMatchTyIRList fn (m :: ms) with (tlHsMatchTyIRList fn ms)
    | Left err = Left (TLHsMatchTyIRList err (m :: ms))
    | Right (nms ** msIR) with (tlHsMatchTyIR fn m)
      | Left err = Left (TLHsMatchTyIRList err (m :: ms))
      | Right mIR = Right (S nms ** mIR :: msIR)

---------------------------------------------------------------------------------------------------
-- [HsDeclTy] -------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

  tlHsDeclTyIR : (d : Haskell98.HsDeclTy)
              -> Either Error (HsDeclTyIR Decl)
  tlHsDeclTyIR (HsFunBind []) =
    Left (TLHsDeclTyIR (StdErr "Function Def. should have at least one clause.") (HsFunBind []))
  tlHsDeclTyIR (HsFunBind (HsMatch l fn ps rhs ws :: ms))
    with (tlHsMatchTyIRList fn (HsMatch l fn ps rhs ws :: ms))
      | Left err =
        Left (TLHsDeclTyIR err (HsFunBind (HsMatch l fn ps rhs ws :: ms)))
      | Right (Z ** clsIR) =
        Left (TLHsDeclTyIR (StdErr "Zero or more matches turned into Zero clauses.")
                          (HsFunBind (HsMatch l fn ps rhs ws :: ms)))
      | Right (S ncls ** clsIR) =
        Right (HsFunBind fn clsIR)
  tlHsDeclTyIR (HsPatBind l p (HsUnGuardedRhs e) ws) with (tlHsDeclTyIRList ws)
    | Left err = Left (TLHsDeclTyIR err (HsPatBind l p (HsUnGuardedRhs e) ws))
    | Right (nws ** wsIR) = Right (HsPatBind p wsIR e)

  tlHsDeclTyIRList : (ds : List Haskell98.HsDeclTy)
                  -> Either Error (nds ** Vect nds (HsDeclTyIR Decl))
  tlHsDeclTyIRList [] = Right (Z ** [])
  tlHsDeclTyIRList (d :: ds) with (tlHsDeclTyIRList ds)
    | Left err = Left (TLHsDeclTyIRList err (d :: ds))
    | Right (nds ** dsIR) with (tlHsDeclTyIR d)
      | Left err = Left (TLHsDeclTyIRList err (d :: ds))
      | Right dIR = Right (S nds ** dIR :: dsIR)

IdMapNameTriple : Type
IdMapNameTriple =
  (Nat, List (k ** (Nat, Nat, Name k, String)), (nvars ** Vect nvars (HsNameTy Variable)))

partial
getVarsDecldInPat : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                 -> (lv : Nat)
                 -> (id : Nat)
                 -> (p : Haskell98.HsPatTy)
                 -> Either Error IdMapNameTriple
getVarsDecldInPat nameMap lv id (HsPVar na) with (tlHsNameTyNew lv id na)
  | Left err = Left err
  | Right (string, (Variable ** na98)) =
    Right (S id,
           (Variable ** (lv, id, getWitness (getHsIdentVarName na98),string)) :: nameMap,
           (S Z ** [na98]))
getVarsDecldInPat nameMap lv id (HsPApp c args) = foldl step (Right (id,nameMap,(Z ** []))) args
  where
    partial
    step : Either Error IdMapNameTriple
        -> Haskell98.HsPatTy
        -> Either Error IdMapNameTriple
    step (Left err) _ = Left err
    step (Right (id', nameMap', (nvars ** vars))) p = getVarsDecldInPat nameMap' lv id' p
  

partial
getVarsDecldInDeclIR : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                    -> (lv : Nat)
                    -> (id : Nat)
                    -> (d : HsDeclTyIR Decl)
                    -> Either Error IdMapNameTriple
getVarsDecldInDeclIR nameMap lv id (HsFunBind fn cls) with (tlHsNameTyNew lv id fn)
  | Left err = Left err
  | Right (string, (Variable ** fn98)) =
    Right (S id,
           (Variable ** (lv,id,getWitness (getHsIdentVarName fn98),string)) :: nameMap,
           (S Z ** [fn98]))
  | Right (_, (Constructor ** fn98)) =
    Left (StdErr "Expecting Variable not Constructor as function name.")
getVarsDecldInDeclIR nameMap lv id (HsPatBind p ws e) =
  getVarsDecldInPat nameMap lv id p

partial
getVarsDecldInDeclsIR : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                     -> (lv : Nat)
                     -> (id : Nat)
                     -> (ds : Vect nds (HsDeclTyIR Decl))
                     -> Either Error (Nat,
                                      List (k ** (Nat, Nat, Name k, String)),
                                      (nvars ** Vect nvars (HsNameTy Variable)))
getVarsDecldInDeclsIR nameMap lv id [] = Right (id, nameMap, (Z ** []))
getVarsDecldInDeclsIR nameMap lv id (d :: ds) with (getVarsDecldInDeclsIR nameMap lv (S id) ds)
  | Left err = Left err
  | Right (id', nameMap', (nvars ** vars)) with (getVarsDecldInDeclIR nameMap' lv id' d)
    | Left err = Left err
    | Right (id'', nameMap'', (nvs ** vs)) = Right (id'', nameMap'', (nvs + nvars ** vs ++ vars))

getNPats : (cls : Vect (S ncls) (HsDeclTyIR FunClause)) -> Nat
getNPats (HsMatch {nps} ps ws e :: cls) = S nps

mutual
  partial
  tlHsMatchTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
            -> (env : Env)
            -> (lv : Nat)
            -> (id : Nat)
            -> (npats : Nat)
            -> (m : HsDeclTyIR FunClause)
            -> Either Error (HsDeclTy env (FunClause npats))
  tlHsMatchTy nameMap env lv id Z m = Left (TLHsMatchTy (StdErr "npats = Z, improbably") m)
  tlHsMatchTy nameMap env lv id (S npats) (HsMatch {nps} ps ws e) =
    case (decEq npats nps) of 
      No _ => Left (TLHsMatchTy (StdErr "Number of patterns do not match.") (HsMatch ps ws e))
      Yes Refl =>
        case tlHsPatTyVect nameMap env lv id ps of
          Left err => Left (TLHsMatchTy err (HsMatch ps ws e))
          Right (id', nameMap', ps98) =>
            case decHsPatSecTy env ps98 of
              No _ => Left (TLHsMatchTy (StdErr "Not (HsPatSecTy env ps98)") (HsMatch ps ws e))
              Yes (Element env_ws psec) =>
                case getVarsDecldInDeclsIR nameMap' (S lv) id' ws of
                  Left err => Left (TLHsMatchTy err (HsMatch ps ws e))
                  Right (id'', nameMap'', (nvars_ws ** vars_ws)) =>
                    case decSameLevel vars_ws of
                      No _ => Left (TLHsMatchTy (StdErr "Not (SameLevel vars_ws)")
                                                (HsMatch ps ws e))
                      Yes sl_ws =>
                        case decEnvAddNewLevel env_ws vars_ws sl_ws of
                          No _ =>
                            Left (TLHsMatchTy
                                    (StdErr "Not (EnvAddNewLevel env_ws vars_ws sl_ws") 
                                    (HsMatch ps ws e))
                          Yes (Element env_e envUpd) =>
                            case tlHsDeclTyList nameMap'' env_e (S (S lv)) id'' vars_ws sl_ws ws of
                              Left err => Left (TLHsMatchTy err (HsMatch ps ws e))
                              Right ws98 =>
                                case tlHsExpTy nameMap'' env_e (S (S lv)) id'' e of
                                  Left err => Left (TLHsMatchTy err (HsMatch ps ws e))
                                  Right e98 =>
                                    Right (HsMatch ps98 {psec=psec} {envUpd=envUpd} e98 ws98)

  partial
  tlHsDeclTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
            -> (env : Env)
            -> (lv : Nat)
            -> (id : Nat)
            -> (vars : Vect nvars (HsNameTy Variable))
            -> (sl : SameLevel vars)
            -> (d : HsDeclTyIR Decl)
            -> Either Error (HsDeclTy env (Decl vars sl))
  tlHsDeclTy nameMap env lv id vars sl (HsFunBind fn cls) with (tlHsNameTy nameMap fn)
    | Left err = Left (TLHsDeclTy err (HsFunBind fn cls))
    | Right (Variable ** fn98) with (isElemEnv env fn98)
      | No _ = Left (TLHsDeclTy (StdErr "Not (ElemEnv fn98 env)") (HsFunBind fn cls))
      | Yes fnInEnv with (Vect.isElem fn98 vars)
        | No _ = Left (TLHsDeclTy (StdErr "Not (Elem fn98 vars") (HsFunBind fn cls))
        | Yes fnInVars with (getNPats cls)
          | Z = Left (TLHsDeclTy (StdErr "npats = Z, improbably.") (HsFunBind fn cls))
          | S npats with (liftErrors (map (tlHsMatchTy nameMap env lv id (S npats)) cls))
            | Left (err :: errs) = Left (TLHsDeclTy (last (err :: errs)) (HsFunBind fn cls))
            | Right cls98 = Right (HsFunBind fn98 {fnInEnv=fnInEnv} {fnInVars=fnInVars} cls98)
    | Right (Constructor ** fn98) =
      Left (TLHsDeclTy (StdErr "Expecting Variable not Constructor function name.")
                       (HsFunBind fn cls))
  tlHsDeclTy nameMap env lv id vars sl (HsPatBind p ws e) with (tlHsPatTyKnown nameMap env p)
    | Left err = Left (TLHsDeclTy err (HsPatBind p ws e))
    | Right p98 with (decHsPatTyElemVars p98 vars)
      | No _ =
        Left (TLHsDeclTy (StdErr "Variables in pattern cannot be found in vars.")
                         (HsPatBind p ws e))
      | Yes pInVars with (decHsPatTyElemEnv env p98)
        | No _ =
          Left (TLHsDeclTy (StdErr "Not (HsPatTyElemEnv env p98)") (HsPatBind p ws e))
        | Yes pInEnv with (getVarsDecldInDeclsIR nameMap (S lv) (S id) ws)
          | Left err = Left (TLHsDeclTy err (HsPatBind p ws e))
          | Right (id', nameMap', (nvars_ws ** vars_ws)) with (decSameLevel vars_ws)
            | No _ = Left (TLHsDeclTy (StdErr "Not (SameLevel vars_ws)") (HsPatBind p ws e))
            | Yes sl_ws with (decEnvAddNewLevel env vars_ws sl_ws)
              | No _ = Left (TLHsDeclTy (StdErr "Not (EnvAddNewLevel env vars_ws sl_ws")
                                        (HsPatBind p ws e))
              | Yes (Element env_e envUpd) with (tlHsDeclTyList nameMap' env_e (S (S lv))
                                                                id' vars_ws sl_ws ws)
                | Left err = Left (TLHsDeclTy err (HsPatBind p ws e))
                | Right ws98 with (tlHsExpTy nameMap' env_e (S (S lv)) id' e)
                  | Left err = Left (TLHsDeclTy err (HsPatBind p ws e))
                  | Right e98 =
                    Right (HsPatBind p98 {pInVars=pInVars} {pInEnv=pInEnv} {envUpd=envUpd} e98 ws98)

  partial
  tlHsDeclTyList : (nameMap : List (k ** (Nat, Nat, Name k, String)))
                -> (env : Env)
                -> (lv : Nat)
                -> (id : Nat)
                -> (vars : Vect nvars (HsNameTy Variable))
                -> (sl : SameLevel vars)
                -> (ds : Vect nds (HsDeclTyIR Decl))
                -> Either Error (Vect nds (HsDeclTy env (Decl vars sl)))
  tlHsDeclTyList nameMap env lv id vars sl [] = Right []
  tlHsDeclTyList nameMap env lv id vars sl (d :: ds) with (tlHsDeclTy nameMap env lv id vars sl d)
    | Left err = Left (TLHsDeclTyList err (d :: ds))
    | Right d98 with (tlHsDeclTyList nameMap env lv id vars sl ds)
      | Left err = Left (TLHsDeclTyList err (d :: ds))
      | Right ds98 = Right (d98 :: ds98)

---------------------------------------------------------------------------------------------------
-- [HsModuleTy] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| HsModuleTy translation function. This should be your starting point.
|||
||| The environment you pass in and the name map should agree (NB this is not checked), and should 
||| contain any Prelude constructors or function names desired/necessary.
|||
||| @nameMap  a mapping of simple string variable names and their more rigorous representation;
|||           have the form (level, unique identifier, name, string name)
partial
tlHsModuleTy : (nameMap : List (k ** (Nat, Nat, Name k, String)))
            -> (env : Env)
            -> (id  : Nat)
            -> Haskell98.HsModuleTy
            -> Either Error (Hs98.HsModuleTy.HsModuleTy)
tlHsModuleTy nameMap env id (HsModule _ _ Nothing [] decls) with (tlHsDeclTyIRList decls)
  | Left err = Left (TLHsModuleTy err)
  | Right (Z ** declsIR) = Left (TLHsModuleTy (StdErr "No declarations does not a module make."))
  | Right (S nds ** declsIR) with (getVarsDecldInDeclsIR nameMap (S Z) id declsIR)
    | Left err = Left (TLHsModuleTy err)
    | Right (_, _, (Z ** vars)) = Left (TLHsModuleTy (StdErr "No variables declared, impossibly."))
    | Right (id', nameMap', (S nvars ** vars)) with (decSameLevel vars)
      | No _ = Left (TLHsModuleTy (StdErr "Collected vars do not have the same level."))
      | Yes sl with (decEnvAddNewLevel env vars sl) 
        | No err = Left (TLHsModuleTy (TyErr (Not (Subset Env (EnvAddNewLevel env vars sl)) ** err))) --(StdErr "Cannot add collected vars to env."))
        | Yes (Element env_ds envRenv_ds) with (tlHsDeclTyList nameMap' env_ds 2
                                                               id' vars sl declsIR)
          | Left err = Left (TLHsModuleTy err)
          | Right decls98 = Right (HsModule env vars {envRenv_ds=envRenv_ds} decls98)
tlHsModuleTy nameMap env id (HsModule _ _ _ _ _) =
  Left (TLHsModuleTy (StdErr "Please ensure that the module has neither imports nor exports."))
