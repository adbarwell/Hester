module IdrisUtils.Data.Vect.Nub

import public Data.Vect

%default total
%access public export

data NumUnique : (xs : Vect m a) -> (n : Nat) -> Type where
  Zero :                                                          NumUnique [] Z
  Succ : (notLater : Not (Elem x xs)) -> (tl : NumUnique xs k) -> NumUnique (x :: xs) (S k)
  Skip : (later : Elem x xs)          -> (tl : NumUnique xs k) -> NumUnique (x :: xs) k

numUnique : DecEq a => (xs : Vect m a) -> Subset Nat (NumUnique xs)
numUnique [] = Element Z Zero
numUnique (x :: xs) with (numUnique xs)
  | Element k tl with (isElem x xs)
    | No  c = Element (S k) (Succ c tl)
    | Yes p = Element k (Skip p tl)

||| This is currently not definable beecause the third case is apparently valid.
|||
||| Define a functor from a -> Nat and use inequalities from there?
||| To do this properly, you should have the functor laws encoded also.
lemma_numUnique_same : DecEq a => {xs : Vect k a} -> NumUnique xs n -> NumUnique xs m -> n = m
-- lemma_numUnique_same {xs = []} Zero Zero = Refl
-- lemma_numUnique_same {xs = (x :: xs)} (Succ notLater tl) (Succ notLater' tl')
--   with (lemma_numUnique_same tl tl')
--     | Refl = Refl
-- lemma_numUnique_same {xs = (x :: xs)} (Succ notLater tl) (Skip later' tl')
--   with (lemma_numUnique_same tl tl')
--     | Refl = notLater later'
-- lemma_numUnique_same {xs = (x :: xs)} (Skip later tl) p2 = ?holeSame_2

||| Propositional nub. Defn. means that we're keeping the *last* occurrence in the list.
data Nub : (xs : Vect m a) -> (nub_xs : Vect n a) -> Type where
  Nil       : Nub [] []
  JustHere  : (notLater : Not (Elem x xs)) -> (tl : Nub xs ys) -> Nub (x :: xs) (x :: ys)
  AlsoThere : (later : Elem x xs) -> (tl : Nub xs ys) -> Nub (x :: xs) ys

nub : DecEq a => (xs : Vect m a) -> (len : NumUnique xs n) -> Subset (Vect n a) (Nub xs)
nub [] Zero = Element [] Nil
nub (x :: xs) (Succ notLater ntl) with (nub xs ntl)
  | Element ys tl = Element (x :: ys) (JustHere notLater tl)
nub (x :: xs) (Skip later ntl) with (nub xs ntl)
  | Element ys tl = Element ys (AlsoThere later tl)

||| This is currently not definable because we need to constrain `n` in the original definiton 
||| better (i.e. using numUnique).
lemma_nub_same : {xs : Vect m a}
              -> {ys : Vect n a}
              -> {zs : Vect k a}
              -> (p1 : Nub xs ys)
              -> (p2 : Nub xs zs)
              -> ys = zs
