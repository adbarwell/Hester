module IdrisUtils.Data.Vect.ConcatQMap

import public Data.Vect

%default total
%access public export

||| Propositional concatMap.
data ConcatQMap : (p   : (x : a) -> (k : Nat) -> Vect k c -> Type)
               -> (xs  : Vect n a)
               -> (m   : Nat)
               -> (yss : Vect m c)
               -> Type where
  Nil : ConcatQMap p [] Z []
  Cons : {p   : (z : a) -> (l : Nat) -> (zs : Vect l c) -> Type}
      -> {k   : Nat}
      -> {ys  : Vect k c}
      -> {m   : Nat}
      -> {yss : Vect m c}
      -> (hd  : p x k ys)
      -> (tl  : ConcatQMap p xs m yss)
      -> ConcatQMap p (x :: xs) (k + m) (ys ++ yss)

concatQMap : {p   : (x : a) -> (k : Nat) -> Vect k c -> Type}
          -> (f   : (x : a) -> (k ** Subset (Vect k c) (p x k)))
          -> (xs  : Vect nxs a)
          -> (nyss ** Subset (Vect nyss c) (ConcatQMap p xs nyss))
concatQMap f [] = (Z ** Element [] Nil)
concatQMap f (x :: xs) with (f x)
  | (k ** Element ys hd) with (concatQMap f xs)
    | (m ** Element yss tl) = (k + m ** Element (ys ++ yss) (Cons hd tl))


lemma_ConcatQMap_injective_len : {p   : (x : a) -> (k : Nat) -> Vect k c -> Type}
                              -> (lemma_p_inj_nys : (x : a) -> (nys, nzs : Nat) -> (ys : Vect nys c) -> (zs : Vect nzs c) -> p x nys ys -> p x nzs zs -> nys = nzs)
                              -> (q : ConcatQMap p xs nyss yss)
                              -> (r : ConcatQMap p xs nzss zss)
                              -> nyss = nzss
lemma_ConcatQMap_injective_len lemma Nil Nil = Refl
lemma_ConcatQMap_injective_len {xs = (x :: xs)} lemma
                                (Cons {k=nys} {ys} q1 q2) (Cons {k=nzs} {ys=zs} r1 r2) =
  case (lemma x nys nzs ys zs  q1 r1, lemma_ConcatQMap_injective_len lemma q2 r2) of
    (Refl, Refl) => Refl

lemma_ConcatQMap_injective : {p   : (x : a) -> (k : Nat) -> Vect k c -> Type}
                          -> (lemma_p_inj : (x : a) -> (n : Nat) -> (ys : Vect n c) -> (zs : Vect n c) -> p x n ys -> p x n zs -> ys = zs)
                          -> (q : ConcatQMap p xs n yss)
                          -> (r : ConcatQMap p xs n zss)
                          -> yss = zss
lemma_ConcatQMap_injective lemma Nil Nil = Refl
lemma_ConcatQMap_injective {xs = (x :: xs)} {n=k+m} lemma
                           (Cons {k=k} {m=m} {ys} q1 q2) (Cons {ys=zs} r1 r2) =
  case (lemma x k ys zs q1 r1, lemma_ConcatQMap_injective lemma q2 r2) of
    (Refl, Refl) => Refl

lemma_ConcatQMap_singleton : {p            : (x : a) -> (k : Nat) -> Vect k c -> Type}
                          -> (lemma_p_sing : (x : a) -> (n : Nat) -> (ys : Vect n c) -> (q,r : p x n ys) -> q = r)
                          -> {xs           : Vect nxs a}
                          -> {nyss         : Nat}
                          -> {yss          : Vect nyss c}
                          -> (s,t          : ConcatQMap p xs nyss yss)
                          -> s = t
lemma_ConcatQMap_singleton lemma Nil Nil = Refl
lemma_ConcatQMap_singleton lemma {nxs = S nxs} {xs = (x :: xs)} {nyss = (k + m)} {yss = (zs ++ zss)}
     (Cons {k=k} {m=m} {ys=zs} {yss=zss} s1 s2) (Cons t1 t2) =
  case (lemma x k zs s1 t1, lemma_ConcatQMap_singleton lemma {xs=xs} {nyss=m} {yss=zss} s2 t2) of
    (Refl, Refl) => Refl
