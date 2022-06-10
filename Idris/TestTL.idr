module TestTL

import IdrisUtils.Utils
import IdrisUtils.Ord

import Haskell98
import Hs98
import TLHaskell98ToHs98
import HaReRenaming
import Transform.Rename
import Hs98Simplified

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Util] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

fromMaybe : (m : Maybe c) -> {auto ok : IsJust m} -> c
fromMaybe (Just x) = x

---------------------------------------------------------------------------------------------------
-- [Dummy SrcLoc] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

loc : SrcLocTy
loc = SrcLoc "" Z Z

---------------------------------------------------------------------------------------------------
-- [Ctrs] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

mkEnvItemCtr : (id : Nat)
            -> (string : String)
            -> Maybe ((Nat, Nat, Name Constructor, String), EnvItem Constructor)
mkEnvItemCtr id string = do
  str <- fromString string
  case strAsConstructor str of
    No _ => Nothing
    Yes ctr => Just ((Z, id, getWitness ctr, string), MkEnvItem id (getWitness ctr))

---------------------------------------------------------------------------------------------------
-- [Vars] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

mkEnvItemVar : (id : Nat) 
            -> (string : String) 
            -> Maybe ((Nat, Nat, Name Variable, String), EnvItem Variable)
mkEnvItemVar id string = do
  str <- fromString string
  case strAsVariable str of
    No _ => Nothing
    Yes var => Just ((Z, id, getWitness var, string), MkEnvItem id (getWitness var))
mkHsIdentVar : (lv, id : Nat) -> (string : String) -> Maybe (HsNameTy Variable)
mkHsIdentVar lv id string = do
  str <- fromString string
  case strAsVariable str of
    No _ => Nothing
    Yes var => Just (HsIdentVar lv id (getWitness var))

---------------------------------------------------------------------------------------------------
-- [Env] ------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

emptyEnv : Env
emptyEnv = MkEnv [] [] {ok=MkUniqueIds Nil Nil Nil Nil Nil}

step : Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), (n ** Vect n (EnvItem Constructor)))
    -> String
    -> Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), (n ** Vect n (EnvItem Constructor)))
step Nothing _ = Nothing
step (Just (id, nameMap, (n ** envitems))) string = do
  (mapping, envitem) <- mkEnvItemCtr id string
  Just (S id, (Constructor ** mapping) :: nameMap, (S n ** envitem :: envitems))

mkEnv0 : (ctrs : List String) -> Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env)
mkEnv0 strings with (foldl step (Just (Z, [], (Z ** []))) strings)
  | Nothing = Nothing
  | Just (id, nameMap, (Z ** [])) = Just (Z, [], emptyEnv)
  | Just (id, nameMap, (S n ** ctrs)) with (decUniqueIds ctrs [])
    | No _ = Nothing
    | Yes ok = Just (id, nameMap, MkEnv ctrs [] {ok=ok})

fromListString : (lvl, id : Nat)
              -> (nameMap : List (k ** (Nat,Nat, Name k, String)))
              -> (funs : List String)
              -> Maybe (Nat,
                        List (k ** (Nat,Nat, Name k, String)),
                        (n ** Vect n (HsNameTy Variable)))
fromListString lvl id nameMap [] = Just (id, nameMap, (Z ** []))
fromListString lvl id nameMap (v :: vs) = do
  v98 <- (mkHsIdentVar lvl id v)
  (id', nameMap', (n ** vs98)) <- fromListString lvl (S id) ((Variable ** (lvl,id,getWitness (getHsIdentVarName v98),v)) :: nameMap) vs
  Just (id', nameMap', (S n ** v98 :: vs98))

addVarsToEnv : (lvl, id : Nat)
            -> (nameMap : List (k ** (Nat,Nat, Name k, String)))
            -> (env : Env)
            -> (funs : List String)
            -> Maybe (Nat, List (k ** (Nat,Nat, Name k, String)), Env)
addVarsToEnv lvl id nameMap env funs = do
  (id', nameMap', (n ** funs98)) <- fromListString lvl id nameMap funs
  case decSameLevel funs98 of
    No _ => Nothing
    Yes sl =>
      case decEnvAddNewLevel env funs98 sl of
        No _ => Nothing
        Yes (Element env' prf) => Just (id', nameMap', env')

mkEnv : (ctrs : List String)
     -> (funs : List String)
     -> (lvl  : Nat)
     -> Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env)
mkEnv ctrs funs lvl = do
  (id, nameMap, env0) <- (mkEnv0 ctrs)
  addVarsToEnv lvl id nameMap env0 funs

PreludeCtrs : List String
-- PreludeCtrs = []
PreludeCtrs = ["Cons", "Nil"]
-- PreludeCtrs = ["True", "False", "Cons", "Nil"]

PreludeFuns : List String
-- PreludeFuns = []
PreludeFuns = ["p"]
-- PreludeFuns = ["p","e"]
-- PreludeFuns = ["plus"]
-- PreludeFuns = ["plus","enum"]
-- PreludeFuns = ["undefined", "plus", "mkList4"]

mkPreludeEnv : Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env)
mkPreludeEnv = mkEnv PreludeCtrs PreludeFuns Z

---------------------------------------------------------------------------------------------------
-- [HsModuleTy] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| f x = x
id : Haskell98.HsModuleTy
id = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 12 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) []]]

||| f x y = x
const : Haskell98.HsModuleTy
const = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 14 1)) (HsIdent "f") [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) []]]

||| f y y = x
constBad : Haskell98.HsModuleTy
constBad = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 14 1)) (HsIdent "f") [HsPVar (HsIdent "y"),HsPVar (HsIdent "y")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) []]]

||| f x = (\y -> (\z -> z) y) x
nestedLambda : Haskell98.HsModuleTy
nestedLambda = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 53 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsApp (HsParen (HsLambda ((SrcLoc "<unknown>" 53 9)) [HsPVar (HsIdent "y")] (HsApp (HsParen (HsLambda ((SrcLoc "<unknown>" 53 16)) [HsPVar (HsIdent "z")] (HsVar (UnQual (HsIdent "z"))))) (HsVar (UnQual (HsIdent "y")))))) (HsVar (UnQual (HsIdent "x"))))) []]]

||| f True x = x 
||| f False x = 42
ifThenElse : Haskell98.HsModuleTy
ifThenElse = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 16 1)) (HsIdent "f") [HsPApp (UnQual (HsIdent "True")) [],HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) [],HsMatch ((SrcLoc "<unknown>" 17 1)) (HsIdent "f") [HsPApp (UnQual (HsIdent "False")) [],HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsLit (HsInt 42))) []]]

||| f x = y where y = 42
whereWithPat : Haskell98.HsModuleTy
whereWithPat = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 19 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "y")))) [HsPatBind ((SrcLoc "<unknown>" 19 15)) (HsPVar (HsIdent "y")) (HsUnGuardedRhs (HsLit (HsInt 42))) []]]]

||| f x = x where x = 42
whereWithShadow : Haskell98.HsModuleTy
whereWithShadow = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 27 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) [HsPatBind ((SrcLoc "<unknown>" 27 15)) (HsPVar (HsIdent "x")) (HsUnGuardedRhs (HsLit (HsInt 42))) []]]]

||| f x = g x 2
|||
||| g x y = y
twoFuns : Haskell98.HsModuleTy
twoFuns = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 21 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "g"))) (HsVar (UnQual (HsIdent "x")))) (HsLit (HsInt 2)))) []],HsFunBind [HsMatch ((SrcLoc "<unknown>" 23 1)) (HsIdent "g") [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "y")))) []]]

||| f x = g x z
|||   where
|||     g x y = h z where h x = x
|||   
|||     z = 42
nestedWheres : Haskell98.HsModuleTy
nestedWheres = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 29 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "g"))) (HsVar (UnQual (HsIdent "x")))) (HsVar (UnQual (HsIdent "z"))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 31 5)) (HsIdent "g") [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")] (HsUnGuardedRhs (HsApp (HsVar (UnQual (HsIdent "h"))) (HsVar (UnQual (HsIdent "z"))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 31 23)) (HsIdent "h") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) []]]],HsPatBind ((SrcLoc "<unknown>" 33 5)) (HsPVar (HsIdent "z")) (HsUnGuardedRhs (HsLit (HsInt 42))) []]]]


||| f x = g x z
|||   where
|||     g x y = h z 
|||     h x = x
|||   
|||     z = 42
nestedWheres2 : Haskell98.HsModuleTy
nestedWheres2 = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 29 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "g"))) (HsVar (UnQual (HsIdent "x")))) (HsVar (UnQual (HsIdent "z"))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 31 5)) (HsIdent "g") [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")] (HsUnGuardedRhs (HsApp (HsVar (UnQual (HsIdent "h"))) (HsVar (UnQual (HsIdent "z"))))) []],HsFunBind [HsMatch ((SrcLoc "<unknown>" 31 23)) (HsIdent "h") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) []], HsPatBind ((SrcLoc "<unknown>" 33 5)) (HsPVar (HsIdent "z")) (HsUnGuardedRhs (HsLit (HsInt 42))) []]]]


||| f x = g x z where
|||   g a b = b
|||   z = 42
simplifiedNestedWheres : Haskell98.HsModuleTy
simplifiedNestedWheres = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 37 1)) (HsIdent "f") [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "g"))) (HsVar (UnQual (HsIdent "x")))) (HsVar (UnQual (HsIdent "z"))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 38 3)) (HsIdent "g") [HsPVar (HsIdent "a"),HsPVar (HsIdent "b")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "b")))) []],HsPatBind ((SrcLoc "<unknown>" 39 3)) (HsPVar (HsIdent "z")) (HsUnGuardedRhs (HsLit (HsInt 42))) []]]]

||| sum n [] = n
||| sum n (h:t) = plus h rest 
|||   where rest = (sumRest n t) where sumRest n t = sum n t 
|||
||| main = sum 0 (enumFromTo 1 4)
pldiBig : Haskell98.HsModuleTy
pldiBig = 
  HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [
    HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "p"))) (HsVar (UnQual (HsIdent "h")))) (HsVar (UnQual (HsIdent "rest"))))) [HsPatBind ((SrcLoc "<unknown>" 48 9)) (HsPVar (HsIdent "rest")) (HsUnGuardedRhs (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "sumRest"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t")))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 48 36)) (HsIdent "sumRest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]]],
    HsPatBind ((SrcLoc "<unknown>" 50 1)) (HsPVar (HsIdent "main")) (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsLit (HsInt 0))) (HsParen (HsApp (HsApp (HsApp (HsApp (HsVar (UnQual (HsIdent "enumFromTo"))) (HsLit (HsInt 1))) (HsLit (HsInt 2))) (HsLit (HsInt 3))) (HsLit (HsInt 4)))))) []
    ]

||| sum n [] = n
||| sum n (h:t) = p h (sum n t)
pldi0 : Haskell98.HsModuleTy
pldi0 =
  HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [
    HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) []]]

||| sum n [] = n
||| sum n (h:t) = plus h rest
|||   where
|||     rest = sumRest n t
|||     sumRest n t = sum n t
pldiMedium : Haskell98.HsModuleTy
pldiMedium = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [
  HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "p"))) (HsVar (UnQual (HsIdent "h")))) (HsVar (UnQual (HsIdent "rest"))))) [HsPatBind ((SrcLoc "<unknown>" 48 3)) (HsPVar (HsIdent "rest")) (HsUnGuardedRhs (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "sumRest"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t")))))) [],HsFunBind [HsMatch ((SrcLoc "<unknown>" 49 3)) (HsIdent "sumRest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]]]


||| sum n [] = n
||| sum n (h:t) = plus h rest
|||   where
|||     rest = sumRest n t
|||     sumRest n t = sum n t
|||
||| main = sum 0 [1..4]
pldiMediumMain : Haskell98.HsModuleTy
pldiMediumMain = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [
  HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "p"))) (HsVar (UnQual (HsIdent "h")))) (HsVar (UnQual (HsIdent "rest"))))) [HsPatBind ((SrcLoc "<unknown>" 49 5)) (HsPVar (HsIdent "rest")) (HsUnGuardedRhs (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t")))))) [],HsFunBind [HsMatch ((SrcLoc "<unknown>" 50 5)) (HsIdent "sumRest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]],
  HsPatBind ((SrcLoc "<unknown>" 52 1)) (HsPVar (HsIdent "main")) (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsLit (HsInt 0))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "e"))) (HsLit (HsInt 1))) (HsLit (HsInt 4)))))) []]

||| sum n [] = n
||| sum n (h:t) = plus h (rest n t)
|||   where
|||     rest n t = sum n t
pldi : Haskell98.HsModuleTy
pldi = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [
  HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "plus"))) (HsVar (UnQual (HsIdent "h")))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "rest"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 48 3)) (HsIdent "rest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]]]

||| sum n [] = n
||| sum n (h:t) = plus h (sum n t)
pldi01 : Haskell98.HsModuleTy
pldi01 = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "plus"))) (HsVar (UnQual (HsIdent "h")))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))))) []]]

||| sum n [] = n
||| sum n (h:t) = plus h (sum n t)
|||   where
|||     sumRest n t = sum n t
||| 
||| main = sum 0 (enumFromTo 1 4)
pldi2Main : Haskell98.HsModuleTy
pldi2Main = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 46 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 47 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "p"))) (HsVar (UnQual (HsIdent "h")))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 49 5)) (HsIdent "rest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]],HsPatBind ((SrcLoc "<unknown>" 51 1)) (HsPVar (HsIdent "main")) (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsLit (HsInt 0))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "e"))) (HsLit (HsInt 1))) (HsLit (HsInt 4)))))) []]

||| sum n [] = n
||| sum n (h:t) = p h (rest n t)
||| where
|||   rest n t = sum n t
pldi3 : Haskell98.HsModuleTy
pldi3 = HsModule ((SrcLoc "<unknown>" 1 1)) (Module "Test") Nothing [] [HsFunBind [HsMatch ((SrcLoc "<unknown>" 55 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPList []] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "n")))) [],HsMatch ((SrcLoc "<unknown>" 56 1)) (HsIdent "sum") [HsPVar (HsIdent "n"),HsPParen (HsPInfixApp (HsPVar (HsIdent "h")) (Special HsCons) (HsPVar (HsIdent "t")))] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "p"))) (HsVar (UnQual (HsIdent "h")))) (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "rest"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))))) [HsFunBind [HsMatch ((SrcLoc "<unknown>" 58 5)) (HsIdent "rest") [HsPVar (HsIdent "n"),HsPVar (HsIdent "t")] (HsUnGuardedRhs (HsApp (HsApp (HsVar (UnQual (HsIdent "sum"))) (HsVar (UnQual (HsIdent "n")))) (HsVar (UnQual (HsIdent "t"))))) []]]]]

partial
evalMod : (env : Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env))
       -> {auto ok : IsJust env}
       -> Haskell98.HsModuleTy
       -> Either TLHaskell98ToHs98.Error (Hs98.HsModuleTy.HsModuleTy)
evalMod (Just (id, nameMap, env)) mod = tlHsModuleTy nameMap env id mod


partial -- thanks to evalMod
testRenameMod : (env : Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env))
             -> {auto ok : IsJust env}
             -> (lv,id : Nat)
             -> (old,new : String)
             -> (m : Haskell98.HsModuleTy)
             -> ErrorOr (Either TLHaskell98ToHs98.Error (Hs98.HsModuleTy.HsModuleTy))
testRenameMod env {ok} lv id old new m with (evalMod env {ok=ok} m)
  | Left err = Just (Left err)
  | Right m98 with (mkHsIdentVar lv id old)
    | Nothing = Err (TyErr ("testRenameMod.mkHsIdentVar.old", lv, id, old))
    | Just old98 with (mkHsIdentVar lv id new)
      | Nothing = Err (TyErr ("testRenameMod.mkHsIdentVar.new", lv, id, new))
      | Just new98 =
        case renameModule lv id old98 new98 m98 of
          Err err => Err err
          Just n => Just (Right n)


partial -- thanks to evalMod
testRenameModPrf : (env : Maybe (Nat, List (k ** (Nat, Nat, Name k, String)), Env))
                -> {auto ok : IsJust env}
                -> (lv,id : Nat)
                -> (old,new : String)
                -> (m : Haskell98.HsModuleTy)
                -> ErrorOr (oldN : Name Variable **
                            newN : Name Variable **
                            m98 : Hs98.HsModuleTy.HsModuleTy **
                            RenamePrf lv id oldN newN m98 (rename lv id oldN newN m98))
testRenameModPrf env {ok} lv id old new m with (evalMod env {ok=ok} m)
  | Left err = Err (TyErr ("testRenameModPrf.evalMod", err))
  | Right m98 with (mkHsIdentVar lv id old)
    | Nothing = Err (TyErr ("testRenameModPrf.mkHsIdentVar.old", lv, id, old))
    | Just (HsIdentVar _ _ old98) with (mkHsIdentVar lv id new)
      | Nothing = Err (TyErr ("testRenameModPrf.mkHsIdentVar.new", lv, id, new))
      | Just (HsIdentVar _ _ new98) =
        Just (old98 ** new98 ** m98 ** prfRename lv id old98 new98 m98)
