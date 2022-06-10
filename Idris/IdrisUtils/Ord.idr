module IdrisUtils.Ord

import Data.Vect

import IdrisUtils.Data.Vect.Map

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Ordering without EQ.
data SOrdering : Type where
  LT : SOrdering
  GT : SOrdering

implementation Uninhabited (Ord.LT = Ord.GT) where
  uninhabited Refl impossible

implementation DecEq SOrdering where
  decEq LT LT = Yes Refl
  decEq GT GT = Yes Refl
  decEq LT GT = No absurd
  decEq GT LT = No (absurd . sym)

||| A strict totally ordering for a given type.
data TotalOrdering : (c : Type) -> Type where
  ||| .
  |||
  ||| For completeness, we should have a term that distinguishes `LT` and `(=)`.
  |||
  ||| @LT       <
  ||| @isLT     decision procedure for `LT`
  ||| @sing     for a given `x` and `xs` there is only one proof of `LTE x xs`
  ||| @irrefl   \forall x,y . (x < y) -> y ≠ x
  ||| @antisym  \forall x,y . (x < y) \/ (y < x)
  ||| @decEq    can probably be inferred (i.e. ¬((x < y) \/ (y < x)) -> x = y) but I'm lazy
  MkTotOrd : (LT      : c -> c -> Type)
          -> (isLT    : (x : c) -> (y : c) -> Dec (LT x y))
          -> (sing    : (x : c) -> (y : c) -> (p : LT x y) -> (q : LT x y) -> p = q)
          -> (irrefl  : (x : c) -> (p : LT x x) -> Void)
          -> (antisym : (x : c) -> (y : c) -> (p : LT x y) -> (q : LT y x) -> Void)
          -> (decEq   : (x : c) -> (y : c) -> Dec (x = y))
          -> TotalOrdering c

interface TotalOrder c where
  order : TotalOrdering c

---------------------------------------------------------------------------------------------------
-- [Projection Functions] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_LT : TotalOrdering c -> (c -> c -> Type)
proj_LT (MkTotOrd lt _ _ _ _ _) = lt

proj_isLT : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Dec (proj_LT ord x y))
proj_isLT (MkTotOrd _ isLT _ _ _ _) = isLT

proj_sing : (ord : TotalOrdering c)
         -> ((x : c) -> (y : c) -> (p : proj_LT ord x y) -> (q : proj_LT ord x y) -> p = q)
proj_sing (MkTotOrd _ _ sing _ _ _) = sing

proj_irrefl : (ord : TotalOrdering c)
           -> ((x : c) -> (p : proj_LT ord x x) -> Void)
proj_irrefl (MkTotOrd _ _ _ irrefl _ _) = irrefl

proj_antisym : (ord : TotalOrdering c)
            -> ((x : c) -> (y : c) -> (p : proj_LT ord x y) -> (q : proj_LT ord y x) -> Void)
proj_antisym (MkTotOrd _ _ _ _ antisym _) = antisym

proj_decEq : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Dec (x = y))
proj_decEq (MkTotOrd _ _ _ _ _ decEq) = decEq

---------------------------------------------------------------------------------------------------
-- [LTE (Derived)] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type where
  IsEq : LTE ord x x
  IsLT : (lt : proj_LT ord x y) -> LTE ord x y

proj_LTE : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Type)
proj_LTE = LTE

isLTE_gt : (neq : Not (x = y)) -> (gt : Not (proj_LT ord x y)) -> LTE ord x y -> Void
isLTE_gt neq gt IsEq = neq Refl
isLTE_gt neq gt (IsLT lt) = gt lt

isLTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_LTE ord x y)
isLTE ord x y with (proj_decEq ord x y)
  isLTE ord y y | Yes Refl = Yes IsEq
  isLTE ord x y | No  neq  with (proj_isLT ord x y)
    isLTE ord x y | No neq | Yes lt = Yes (IsLT lt)
    isLTE ord x y | No neq | No  gt = No (isLTE_gt neq gt)

---------------------------------------------------------------------------------------------------
-- [GT (Derived)] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_GT : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type
proj_GT ord x y = proj_LT ord y x

isGT : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_GT ord x y)
isGT ord x y = proj_isLT ord y x

proj_GTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type
proj_GTE ord x y = proj_LTE ord y x

isGTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_GTE ord x y)
isGTE ord x y = isLTE ord y x
