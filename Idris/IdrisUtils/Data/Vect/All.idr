module IdrisUtils.Data.Vect.All

import public Data.Vect

%default total
%access public export

||| A proposition `p` holds for all elements in `xs`
data All : (p : a -> Type) -> (xs : Vect n a) -> Type where
  Nil  : All p []
  (::) : (hd : p x) -> (tl : All p xs) -> All p (x :: xs)

decAll : {p : a -> Type} -> (decP : (x : a) -> Dec (p x)) -> (xs : Vect n a) -> Dec (All p xs)
decAll decP [] = Yes Nil
decAll decP (x :: xs) with (decP x)
  | No contra = No (\(hd :: tl) => contra hd)
  | Yes hd  with (decAll decP xs)
    | No contra = No (\(hd :: tl) => contra tl)
    | Yes tl = Yes (hd :: tl)

lemma_All_singleton : {xs : Vect n c}
                   -> {r : c -> Type} 
                   -> (lemma_r : (z : c) -> (x : r z) -> (y : r z) -> x = y)
                   -> (p,q : All r xs)
                   -> p = q
lemma_All_singleton lemma Nil Nil = Refl
lemma_All_singleton lemma {xs = y :: ys} (p :: ps) (q :: qs) =
  case (lemma y p q, lemma_All_singleton lemma ps qs) of (Refl, Refl) => Refl

