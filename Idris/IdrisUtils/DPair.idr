module IdrisUtils.DPair

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Applies some relation to the witness inside a dependent pair.
data Fst : {p : a -> Type} -> (x : a ** p x) -> a -> Type where
  MkFst : Fst (x ** prf) x

fst : {p : a -> Type} -> (pair : (x : a ** p x)) -> Subset a (Fst pair)
fst (x ** prf) = Element x MkFst

data Snd : {p : a -> Type} -> (x : a ** p x) -> (p y) -> Type where
  MkSnd : Snd (x ** prf) prf

snd : {p : a -> Type} -> (pair : (x : a ** p x)) -> Subset (p (Pairs.DPair.fst pair)) (Snd pair)
snd (x ** prf) = Element prf MkSnd
