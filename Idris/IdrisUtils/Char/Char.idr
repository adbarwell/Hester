module IdrisUtils.Char.Char

import Data.Vect

import IdrisUtils.Char.CharKind
import IdrisUtils.Char.PChar
import IdrisUtils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Char] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Char : Type where
  MkChar : PChar v (k,i) -> Char.Char

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTChar : (x,y : Char.Char) -> Type where
  IsLTChar : (lt : LTPChar x y) -> LTChar (MkChar x) (MkChar y)

isLTChar : (x,y : Char.Char) -> Dec (LTChar x y)
isLTChar (MkChar x) (MkChar y) with (isLTPChar x y)
  | No gte = No (\(IsLTChar lt) => gte lt)
  | Yes lt = Yes (IsLTChar lt)

singLTChar : (x,y : Char.Char) -> (p,q : LTChar x y) -> p = q
singLTChar (MkChar x) (MkChar y) (IsLTChar p) (IsLTChar q) =
  case singLTPChar x y p q of Refl => Refl

irreflLTChar : (x : Char.Char) -> (p : LTChar x x) -> Void
irreflLTChar (MkChar x) (IsLTChar p) = irreflLTPChar x p

antisymLTChar : (x,y : Char.Char) -> (p : LTChar x y) -> (q : LTChar y x) -> Void
antisymLTChar (MkChar x) (MkChar y) (IsLTChar p) (IsLTChar q) = antisymLTPChar x y p q

implementation Equality.DecEq Char.Char where
  decEq (MkChar x) (MkChar y) with (decEq x y)
    decEq (MkChar y) (MkChar y) | Yes Refl = Yes Refl
    decEq (MkChar x) (MkChar y) | No  neq  = No (\Refl => neq Refl)

TotalOrderingChar : TotalOrdering Char.Char
TotalOrderingChar = MkTotOrd LTChar isLTChar singLTChar irreflLTChar antisymLTChar decEq

---------------------------------------------------------------------------------------------------
-- [CharAsNat] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data CharAsNat : Char.Char -> Nat -> Type where
  MkCharAsNat : CharKindAsNat k n -> CharAsNat (MkChar {k} {i} x) (i + n)

---------------------------------------------------------------------------------------------------
-- [Char Kinds] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Minuscule : Char.Char -> Type where
  IsUndscr : Minuscule (MkChar C_)
  IsMin1st : Minuscule (MkChar {k = Min1st} x)
  IsMin2nd : Minuscule (MkChar {k = Min2nd} x)
  IsMin3rd : Minuscule (MkChar {k = Min3rd} x)

data Majuscule : Char.Char -> Type where
  IsMaj1st : Majuscule (MkChar {k = Maj1st} x)
  IsMaj2nd : Majuscule (MkChar {k = Maj2nd} x)
  IsMaj3rd : Majuscule (MkChar {k = Maj3rd} x)

data Numeral : Char.Char -> Type where
  IsNum : Numeral (MkChar {k = Num} x)

data Prime : Char.Char -> Type where
  IsPri : Prime (MkChar C')
