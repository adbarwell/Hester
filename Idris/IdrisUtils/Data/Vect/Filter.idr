module IdrisUtils.Data.Vect.Filter

import Data.Vect

import IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Propositional filter.
|||
||| Two vectors are related via the unary relation `p` s.t. `ys` contains only those elements in
||| `xs` for which `p` holds.
data Filter : (prop : c -> Prop)
           -> (xs : Vect n c)
           -> (m : Nat)
           -> (ys : Vect m (Subset c (\x => proj_P (prop x))))
           -> Type where
  Nil : Filter prop [] Z []
  Yea : (hd : proj_P (prop x))
     -> (tl : Filter prop xs nys ys)
     -> Filter prop (x :: xs) (S nys) (Element x hd :: ys)
  Nay : (hd : proj_Q (prop x)) -> (tl : Filter prop xs nys ys) -> Filter prop (x :: xs) nys ys

---------------------------------------------------------------------------------------------------
-- [Covering Function] ----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

filter : {prop : c -> Prop}
      -> (dec  : (x : c) -> Decidable (prop x))
      -> (xs   : Vect n c)
      -> (nys ** (Subset (Vect nys (Subset c (\x => proj_P (prop x)))) (Filter prop xs nys)))
filter {prop} dec [] = (Z ** Element [] Nil)
filter {prop} dec (x :: xs) with (filter dec xs)
  | (nys ** Element ys tl) with (decP (dec x))
    | No  hd = (nys ** Element ys (Nay hd tl))
    | Yes hd = (S nys ** Element (Element x hd :: ys) (Yea hd tl))

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
