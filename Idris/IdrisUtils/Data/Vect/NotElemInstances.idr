module IdrisUtils.Data.Vect.NotElemInstances

import IdrisUtils.Ord
import IdrisUtils.Nat
import IdrisUtils.Char
import IdrisUtils.Data.String

import Data.Vect
import IdrisUtils.Data.Vect.NotElem

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Instances] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

NotElemNat : (x : Nat) -> (xs : Vect n Nat) -> Type
NotElemNat = NotElem TotalOrderingNat

NotElemChar : (x : Char.Char) -> (xs : Vect n Char.Char) -> Type 
NotElemChar = NotElem TotalOrderingChar

NotElemStr : Str -> (xs : Vect n Str) -> Type
NotElemStr = NotElem TotalOrderingStr