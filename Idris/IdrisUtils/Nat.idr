module IdrisUtils.Nat

import IdrisUtils.Decidability
import IdrisUtils.NotEq
import IdrisUtils.Ord

import Data.Vect
import IdrisUtils.Data.Vect.NotElem
import IdrisUtils.Data.Vect.IsSet

%default total
%access public export

-- [Naturals] -------------------------------------------------------------------------------------

data IsZero : Nat -> Type where
  ItIsZero : IsZero Z

implementation Uninhabited (IsZero (S k)) where
  uninhabited ItIsZero impossible

decIsZero : (k : Nat) -> Dec (IsZero k)
decIsZero Z     = Yes ItIsZero
decIsZero (S k) = No absurd

data IsOne : Nat -> Type where
  ItIsOne : IsOne (S Z)

implementation Uninhabited (IsOne Z) where
  uninhabited ItIsOne impossible
implementation Uninhabited (IsOne (S (S k))) where
  uninhabited ItIsOne impossible

decIsOne : (k : Nat) -> Dec (IsOne k)
decIsOne Z         = No absurd
decIsOne (S Z)     = Yes ItIsOne
decIsOne (S (S k)) = No absurd

-- [Inequalities] ---------------------------------------------------------------------------------

data LTNat : Nat -> Nat -> Type where
  LTZero : LTNat Z (S k)
  LTSucc : LTNat n m -> LTNat (S n) (S m)

GTNat : Nat -> Nat -> Type
GTNat x y = LTNat y x

implementation Uninhabited (LTNat _ Z) where
  uninhabited LTZero impossible
  uninhabited LTSucc impossible

isLTNat : (n : Nat) -> (m : Nat) -> Dec (LTNat n m)
isLTNat _     Z     = No absurd
isLTNat Z     (S m) = Yes LTZero
isLTNat (S n) (S m) =
  case (isLTNat n m) of
    No nGTEm => No (\(LTSucc nLTm) => nGTEm nLTm)
    Yes nLTm => Yes (LTSucc nLTm)

singLTNat : (x, y : Nat) -> (p : LTNat x y) -> (q : LTNat x y) -> (p = q)
singLTNat Z (S y) LTZero LTZero = Refl
singLTNat (S x) (S y) (LTSucc nLTm_1) (LTSucc nLTm_2) =
  case (singLTNat x y nLTm_1 nLTm_2) of
    Refl => Refl

irreflLTNat : (x : Nat) -> (p : LTNat x x) -> Void
irreflLTNat x LTZero impossible
irreflLTNat (S x) (LTSucc p) = irreflLTNat x p

antisymLTNat : (x, y : Nat) -> (p : LTNat x y) -> (q : LTNat y x) -> Void
antisymLTNat Z (S y) LTZero _ impossible
antisymLTNat (S x) (S y) (LTSucc p) (LTSucc q) with (antisymLTNat x y p q) | void = void

-- [Ordering] -------------------------------------------------------------------------------------

TotalOrderingNat : TotalOrdering Nat
TotalOrderingNat = MkTotOrd LTNat isLTNat singLTNat irreflLTNat antisymLTNat decEq

-- [Set] ------------------------------------------------------------------------------------------

IsSetNat : (xs : Vect n Nat) -> Type
IsSetNat = IsSet TotalOrderingNat

-- [Decidability] ---------------------------------------------------------------------------------

lemma_LT_sound : (x, y : Nat) -> (LTNat x y) -> Not (LTE y x)
lemma_LT_sound Z (S y) LTZero p = absurd p
lemma_LT_sound (S x) (S y) (LTSucc lt) (LTESucc lte) = lemma_LT_sound x y lt lte

lemma_LTE_sound : (x,y : Nat) -> (LTE y x) -> Not (LTNat x y)
lemma_LTE_sound x Z LTEZero p = absurd p
lemma_LTE_sound (S x) (S y) (LTESucc lte) (LTSucc lt) = lemma_LTE_sound x y lte lt

PropNat : (x,y : Nat) -> Prop
PropNat x y = MkProp (LTNat x y) (LTE y x)
                     (isLTNat x y) (isLTE y x)
                     (lemma_LT_sound x y) (lemma_LTE_sound x y)

decLTNat : (x,y : Nat) -> Dec (PropNat x y)
decLTNat Z Z = No LTEZero
decLTNat (S x) Z = No LTEZero
decLTNat Z (S y) = Yes LTZero
decLTNat (S x) (S y) with (decLTNat x y)
  | Yes p = Yes (LTSucc p)
  | No  q = No (LTESucc q)

DecidableNat : (x,y : Nat) -> Decidable (PropNat x y)
DecidableNat x y = IsDecidable (decLTNat x y)
