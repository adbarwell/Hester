module IdrisUtils.Char

import Data.Vect

import public IdrisUtils.Char.CharKind
import public IdrisUtils.Char.PChar
import public IdrisUtils.Char.Char

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [CharAsNat] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Covering Function] ----------------------------------------------------------------------------

charAsNat : (x : Char.Char) -> Subset Nat (CharAsNat x)
charAsNat (MkChar {k} {i} x) with (charKindAsNat k)
  | Element n p = Element (i + n) (MkCharAsNat p)

-- [Properties] -----------------------------------------------------------------------------------

lemma_CharAsNat_injective : (p : CharAsNat x n) -> (q : CharAsNat x m) -> n = m
lemma_CharAsNat_injective (MkCharAsNat p) (MkCharAsNat q) =
  case lemma_CharKindAsNat_injection p q of Refl => Refl

lemma_CharAsNat_singleton : (p,q : CharAsNat x n) -> p = q
lemma_CharAsNat_singleton (MkCharAsNat SymAsNat) (MkCharAsNat SymAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat NumAsNat) (MkCharAsNat NumAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Min1stAsNat) (MkCharAsNat Min1stAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Min2ndAsNat) (MkCharAsNat Min2ndAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Min3rdAsNat) (MkCharAsNat Min3rdAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Maj1stAsNat) (MkCharAsNat Maj1stAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Maj2ndAsNat) (MkCharAsNat Maj2ndAsNat) = Refl
lemma_CharAsNat_singleton (MkCharAsNat Maj3rdAsNat) (MkCharAsNat Maj3rdAsNat) = Refl

---------------------------------------------------------------------------------------------------
-- [Minuscule] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Utilities] ------------------------------------------------------------------------------------

implementation Uninhabited (Minuscule (MkChar C')) where
  uninhabited IsUndscr impossible
  uninhabited IsMin1st impossible
  uninhabited IsMin2nd impossible
  uninhabited IsMin3rd impossible

min_not_num : (x : PChar v (Num,i)) -> Minuscule (MkChar x) -> Void
min_not_num x IsUndscr impossible
min_not_num x IsMin1st impossible
min_not_num x IsMin2nd impossible
min_not_num x IsMin3rd impossible

min_not_maj1st : (x : PChar v (Maj1st,i)) -> Minuscule (MkChar x) -> Void
min_not_maj1st x IsUndscr impossible
min_not_maj1st x IsMin1st impossible
min_not_maj1st x IsMin2nd impossible
min_not_maj1st x IsMin3rd impossible

min_not_maj2nd : (x : PChar v (Maj2nd,i)) -> Minuscule (MkChar x) -> Void
min_not_maj2nd x IsUndscr impossible
min_not_maj2nd x IsMin1st impossible
min_not_maj2nd x IsMin2nd impossible
min_not_maj2nd x IsMin3rd impossible

min_not_maj3rd : (x : PChar v (Maj3rd,i)) -> Minuscule (MkChar x) -> Void
min_not_maj3rd x IsUndscr impossible
min_not_maj3rd x IsMin1st impossible
min_not_maj3rd x IsMin2nd impossible
min_not_maj3rd x IsMin3rd impossible

-- [Decision Procedure] ---------------------------------------------------------------------------

isMinuscule : (x : Char.Char) -> Dec (Minuscule x)
isMinuscule (MkChar {k = Sym} C_)   = Yes IsUndscr
isMinuscule (MkChar {k = Sym} C')   = No absurd
isMinuscule (MkChar {k = Num} x)    = No (min_not_num x)
isMinuscule (MkChar {k = Min1st} x) = Yes IsMin1st
isMinuscule (MkChar {k = Min2nd} x) = Yes IsMin2nd
isMinuscule (MkChar {k = Min3rd} x) = Yes IsMin3rd
isMinuscule (MkChar {k = Maj1st} x) = No (min_not_maj1st x)
isMinuscule (MkChar {k = Maj2nd} x) = No (min_not_maj2nd x)
isMinuscule (MkChar {k = Maj3rd} x) = No (min_not_maj3rd x)

-- [Properties] -----------------------------------------------------------------------------------

lemma_Minuscule_singleton : (p, q : Minuscule x) -> p = q
lemma_Minuscule_singleton IsUndscr IsUndscr = Refl
lemma_Minuscule_singleton IsMin1st IsMin1st = Refl
lemma_Minuscule_singleton IsMin2nd IsMin2nd = Refl
lemma_Minuscule_singleton IsMin3rd IsMin3rd = Refl

---------------------------------------------------------------------------------------------------
-- [Majuscule] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Utilities] ------------------------------------------------------------------------------------

implementation Uninhabited (Majuscule (MkChar C_)) where
  uninhabited IsMaj1st impossible
  uninhabited IsMaj2nd impossible
  uninhabited IsMaj3rd impossible
implementation Uninhabited (Majuscule (MkChar C')) where
  uninhabited IsMaj1st impossible
  uninhabited IsMaj2nd impossible
  uninhabited IsMaj3rd impossible

maj_not_num : (x : PChar v (Num,i)) -> Majuscule (MkChar x) -> Void
maj_not_num x IsMaj1st impossible
maj_not_num x IsMaj2nd impossible
maj_not_num x IsMaj3rd impossible

maj_not_min1st : (x : PChar v (Min1st,i)) -> Majuscule (MkChar x) -> Void
maj_not_min1st x IsMaj1st impossible
maj_not_min1st x IsMaj2nd impossible
maj_not_min1st x IsMaj3rd impossible

maj_not_min2nd : (x : PChar v (Min2nd,i)) -> Majuscule (MkChar x) -> Void
maj_not_min2nd x IsMaj1st impossible
maj_not_min2nd x IsMaj2nd impossible
maj_not_min2nd x IsMaj3rd impossible

maj_not_min3rd : (x : PChar v (Min3rd,i)) -> Majuscule (MkChar x) -> Void
maj_not_min3rd x IsMaj1st impossible
maj_not_min3rd x IsMaj2nd impossible
maj_not_min3rd x IsMaj3rd impossible

-- [Decision Procedure] ---------------------------------------------------------------------------

isMajuscule : (x : Char.Char) -> Dec (Majuscule x)
isMajuscule (MkChar {k = Sym} C_)   = No absurd
isMajuscule (MkChar {k = Sym} C')   = No absurd
isMajuscule (MkChar {k = Num} x)    = No (maj_not_num x)
isMajuscule (MkChar {k = Min1st} x) = No (maj_not_min1st x)
isMajuscule (MkChar {k = Min2nd} x) = No (maj_not_min2nd x)
isMajuscule (MkChar {k = Min3rd} x) = No (maj_not_min3rd x)
isMajuscule (MkChar {k = Maj1st} x) = Yes IsMaj1st
isMajuscule (MkChar {k = Maj2nd} x) = Yes IsMaj2nd
isMajuscule (MkChar {k = Maj3rd} x) = Yes IsMaj3rd

-- [Properties] -----------------------------------------------------------------------------------

lemma_Majuscule_singleton : (p, q : Majuscule x) -> p = q
lemma_Majuscule_singleton IsMaj1st IsMaj1st = Refl
lemma_Majuscule_singleton IsMaj2nd IsMaj2nd = Refl
lemma_Majuscule_singleton IsMaj3rd IsMaj3rd = Refl

---------------------------------------------------------------------------------------------------
-- [Numeral] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Utilities] ------------------------------------------------------------------------------------

implementation Uninhabited (Numeral (MkChar C_)) where
  uninhabited IsNum impossible
implementation Uninhabited (Numeral (MkChar C')) where
  uninhabited IsNum impossible
  
num_not_min1st : (x : PChar v (Min1st,i)) -> Numeral (MkChar x) -> Void
num_not_min1st x IsNum impossible

num_not_min2nd : (x : PChar v (Min2nd,i)) -> Numeral (MkChar x) -> Void
num_not_min2nd x IsNum impossible

num_not_min3rd : (x : PChar v (Min3rd,i)) -> Numeral (MkChar x) -> Void
num_not_min3rd x IsNum impossible
  
num_not_maj1st : (x : PChar v (Maj1st,i)) -> Numeral (MkChar x) -> Void
num_not_maj1st x IsNum impossible

num_not_maj2nd : (x : PChar v (Maj2nd,i)) -> Numeral (MkChar x) -> Void
num_not_maj2nd x IsNum impossible

num_not_maj3rd : (x : PChar v (Maj3rd,i)) -> Numeral (MkChar x) -> Void
num_not_maj3rd x IsNum impossible

-- [Decision Procedure] ---------------------------------------------------------------------------

isNumeral : (x : Char.Char) -> Dec (Numeral x)
isNumeral (MkChar {k = Sym} C_)   = No absurd
isNumeral (MkChar {k = Sym} C')   = No absurd
isNumeral (MkChar {k = Num} x)    = Yes IsNum
isNumeral (MkChar {k = Min1st} x) = No (num_not_min1st x)
isNumeral (MkChar {k = Min2nd} x) = No (num_not_min2nd x)
isNumeral (MkChar {k = Min3rd} x) = No (num_not_min3rd x)
isNumeral (MkChar {k = Maj1st} x) = No (num_not_maj1st x)
isNumeral (MkChar {k = Maj2nd} x) = No (num_not_maj2nd x)
isNumeral (MkChar {k = Maj3rd} x) = No (num_not_maj3rd x)

-- [Properties] -----------------------------------------------------------------------------------

lemma_Numeral_singleton : (p, q : Numeral x) -> p = q
lemma_Numeral_singleton IsNum IsNum = Refl

---------------------------------------------------------------------------------------------------
-- [Prime] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Utilities] ------------------------------------------------------------------------------------

implementation Uninhabited (Prime (MkChar C_)) where
  uninhabited IsPri impossible

pri_not_num : (x : PChar v (Num,i)) -> Prime (MkChar x) -> Void
pri_not_num x IsPri impossible

pri_not_min1st : (x : PChar v (Min1st,i)) -> Prime (MkChar x) -> Void
pri_not_min1st x IsPri impossible

pri_not_min2nd : (x : PChar v (Min2nd,i)) -> Prime (MkChar x) -> Void
pri_not_min2nd x IsPri impossible

pri_not_min3rd : (x : PChar v (Min3rd,i)) -> Prime (MkChar x) -> Void
pri_not_min3rd x IsPri impossible
  
pri_not_maj1st : (x : PChar v (Maj1st,i)) -> Prime (MkChar x) -> Void
pri_not_maj1st x IsPri impossible

pri_not_maj2nd : (x : PChar v (Maj2nd,i)) -> Prime (MkChar x) -> Void
pri_not_maj2nd x IsPri impossible

pri_not_maj3rd : (x : PChar v (Maj3rd,i)) -> Prime (MkChar x) -> Void
pri_not_maj3rd x IsPri impossible

-- [Decision Procedure] ---------------------------------------------------------------------------

isPrime : (x : Char.Char) -> Dec (Prime x)
isPrime (MkChar {k = Sym} C_)   = No absurd
isPrime (MkChar {k = Sym} C')   = Yes IsPri
isPrime (MkChar {k = Num} x)    = No (pri_not_num x)
isPrime (MkChar {k = Min1st} x) = No (pri_not_min1st x)
isPrime (MkChar {k = Min2nd} x) = No (pri_not_min2nd x)
isPrime (MkChar {k = Min3rd} x) = No (pri_not_min3rd x)
isPrime (MkChar {k = Maj1st} x) = No (pri_not_maj1st x)
isPrime (MkChar {k = Maj2nd} x) = No (pri_not_maj2nd x)
isPrime (MkChar {k = Maj3rd} x) = No (pri_not_maj3rd x)

-- [Properties] -----------------------------------------------------------------------------------

lemma_Prime_singleton : (p, q : Prime x) -> p = q
lemma_Prime_singleton IsPri IsPri = Refl

---------------------------------------------------------------------------------------------------
-- [Convenience] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

toChar : Char.Char -> Char
toChar (MkChar {v} x) = v
