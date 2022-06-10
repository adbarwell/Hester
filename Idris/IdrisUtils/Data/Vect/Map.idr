module IdrisUtils.Data.Vect.Map

import Data.Vect

%default total
%access public export

||| Propositional map.
|||
||| Two lists are related via the binary relation `p`.
data Map : (p : a -> b -> Type) -> (xs : Vect k a) -> (ys : Vect k b) -> Type where
  Nil  : Map p [] []
  (::) : (hd : p x y) -> (tl : Map p xs ys) -> Map p (x :: xs) (y :: ys)

map : {p  : a -> b -> Type}
   -> (f  : (x : a) -> Subset b (p x))
   -> (xs : Vect k a)
   -> Subset (Vect k b) (Map p xs)
map {p} f [] = Element [] Nil
map {p} f (x :: xs) with (f x)
  | Element y hd with (map {p=p} f xs)
    | Element ys tl = Element (y :: ys) (hd :: tl)


lemma_Map_injective : (lemma_r_injective : (x : a) -> (y,z : b) -> r x y -> r x z -> y = z)
                   -> {xs : Vect n a}
                   -> {ys : Vect n b}
                   -> {zs : Vect n b}
                   -> (p : Map r xs ys)
                   -> (q : Map r xs zs)
                   -> ys = zs
lemma_Map_injective lemma Nil Nil = Refl
lemma_Map_injective lemma {xs = (x :: xs)} {ys = (y :: ys)} {zs = (z :: zs)}
                    (hd_p :: tl_p) (hd_q :: tl_q) =
  case (lemma x y z hd_p hd_q, lemma_Map_injective lemma tl_p tl_q) of
    (Refl, Refl) => Refl

lemma_Map_singleton : (lemma_r_singleton : (x : a) -> (y : b)
                                        -> (p : r x y) -> (q : r x y) -> p = q)
                   -> {xs : Vect n a}
                   -> {ys : Vect n b}
                   -> (p  : Map r xs ys)
                   -> (q  : Map r xs ys)
                   -> p = q
lemma_Map_singleton lemma {xs = []} {ys = []} Nil Nil = Refl
lemma_Map_singleton lemma {xs = (x :: xs)} {ys = (y :: ys)} (hd_p :: tl_p) (hd_q :: tl_q) =
  case (lemma x y hd_p hd_q, lemma_Map_singleton lemma tl_p tl_q) of
    (Refl, Refl) => Refl
