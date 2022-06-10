module IdrisUtils.Utils

import public Data.Vect

import public IdrisUtils.Char
import public IdrisUtils.Decidability
import public IdrisUtils.DPair
import public IdrisUtils.Fin
import public IdrisUtils.Maybe
import public IdrisUtils.Nat
import public IdrisUtils.NotEq

import public IdrisUtils.Data.String
import public IdrisUtils.Data.Vect
import public IdrisUtils.Data.Vect.All
import public IdrisUtils.Data.Vect.ConcatQMap
import public IdrisUtils.Data.Vect.Elem
import public IdrisUtils.Data.Vect.ElemInstances
import public IdrisUtils.Data.Vect.Filter
import public IdrisUtils.Data.Vect.IsSet
import public IdrisUtils.Data.Vect.Map
import public IdrisUtils.Data.Vect.Maximum
import public IdrisUtils.Data.Vect.NotElem
import public IdrisUtils.Data.Vect.NotElemInstances
import public IdrisUtils.Data.Vect.Sum

%default total
%access public export

-- [Finite Sets] ----------------------------------------------------------------------------------

data IsZero : Fin n -> Type where
  MkIsZero : IsZero FZ

data IsOne : Fin n -> Type where
  MkIsOne : IsOne (FS FZ)

-- [DecEq] ----------------------------------------------------------------------------------------

implementation Uninhabited (Vect.Here = Vect.There later) where
  uninhabited Refl impossible

implementation Equality.DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There later) = No absurd
  decEq (There later) Here = No (absurd . sym)
  decEq (There later) (There x) with (decEq later x)
    decEq (There x) (There x) | Yes Refl = Yes Refl
    decEq (There later) (There x) | No c = No (\Refl => c Refl)
