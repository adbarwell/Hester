module IdrisUtils.Maybe

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Certainly : (m : Maybe a) -> (x : a) -> Type where
  MkCertainly : Certainly (Just x) x

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Certainly_injective : (m : Maybe a) -> (x,y : a)
                         -> (p : Certainly m x) -> (q : Certainly m y)
                         -> x = y
lemma_Certainly_injective (Just z) z z MkCertainly MkCertainly = Refl

lemma_Certainly_singleton : (m : Maybe a) -> (x : a)
                         -> (p : Certainly m x) -> (q : Certainly m x) -> p = q
lemma_Certainly_singleton (Just x) x MkCertainly MkCertainly = Refl
