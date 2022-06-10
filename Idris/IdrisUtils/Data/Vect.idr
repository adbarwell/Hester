module IdrisUtils.Data.Vect

import public Data.Vect

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

decEqVect : DecEq c => (xs : Vect n c) -> (ys : Vect m c) -> Dec (xs = ys)
decEqVect {n = n} {m = m} xs ys with (decEq n m)
  decEqVect {n = n} {m = m} xs ys | No neq = No (decEqVect_len neq) where
    decEqVect_len : {vs : Vect nvs c} -> {ws : Vect nws c}
                 -> (contra : Not (nvs = nws)) -> Not (vs = ws)
    decEqVect_len {nvs = nvs} {nws = nvs} contra Refl = contra Refl
  decEqVect {n = n} {m = n} xs ys | Yes Refl with (decEq xs ys)
    decEqVect {n = n} {m = n} xs ys | Yes Refl | No neq = No (\Refl => neq Refl)
    decEqVect {n = n} {m = n} xs xs | Yes Refl | Yes Refl = Yes Refl
