module IdrisUtils.Data.Vect.Sum

import public Data.Vect

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Propositional sum.
|||
||| `sum . (map f)`
data Sum : (p : a -> Nat -> Type) -> (xs : Vect k a) -> (sum : Nat) -> Type where
  Nil  : Sum p [] Z
  (::) : (hd : p x m) -> (tl : Sum p xs n) -> Sum p (x :: xs) (plus m n)

sum : (f : (x : a) -> Subset Nat (p x))
   -> (xs : Vect k a)
   -> Subset Nat (Sum p xs)
sum f [] = Element Z Nil
sum f (x :: xs) with (f x)
  | Element m q with (sum f xs)
    | Element n r = Element (plus m n) (q :: r)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Sum_injective : (lemma_p_inj : {n,m : Nat} -> {x : a} -> p x n -> p x m -> n = m)
                   -> {xs : Vect k a} -> Sum p xs s -> Sum p xs t -> s = t
lemma_Sum_injective lemma Nil Nil = Refl
lemma_Sum_injective lemma (hd1 :: tl1) (hd2 :: tl2)
  with (lemma hd1 hd2, lemma_Sum_injective lemma tl1 tl2)
   | (Refl, Refl) = Refl

lemma_Sum_singleton : (lemma_p_sing : {n : Nat} -> {x : c} -> (p,q : r x n) -> p = q)
                   -> (p : Sum r xs s) -> (q : Sum r xs s) -> p = q
lemma_Sum_singleton lemma Nil Nil = Refl
lemma_Sum_singleton lemma ((::) {m} {n} hd_p tl_p) ((::) {m=m} {n=n} hd_q tl_q) =
  case (lemma hd_p hd_q, lemma_Sum_singleton lemma tl_p tl_q) of (Refl, Refl) => Refl
