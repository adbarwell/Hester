module IdrisUtils.Data.Vect.Maximum

import public Data.Vect

import IdrisUtils.Data.Vect.All

import IdrisUtils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Maximum : (ord : TotalOrdering c) -> (xs : Vect n c) -> (max : c) -> Type where
  MkMaximum : {max : c} -> (gte : All (proj_GTE ord max) xs) -> Maximum ord xs max

decMaximum : (ord : TotalOrdering c) -> (xs  : Vect n c) -> (max : c) -> Dec (Maximum ord xs max)
decMaximum ord xs max with (decAll (isGTE ord max) xs)
  | No ngte = No (\(MkMaximum gte) => ngte gte)
  | Yes gte = Yes (MkMaximum gte)

maximum : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> c
maximum ord x y with (isGT ord x y)
  | No  _ = y
  | Yes _ = x
