module IdrisUtils.Data.Vect.ElemInstances

import Data.Vect

import IdrisUtils.Data.Vect.Elem

import IdrisUtils.Char
import IdrisUtils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Instances] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

ElemChar : (x : Char.Char) -> (xs : Vect n Char.Char) -> Type 
ElemChar = Elem TotalOrderingChar
