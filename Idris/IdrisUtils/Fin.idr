module IdrisUtils.Fin

import public Data.Fin

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data FinToNat : (fin : Fin ub) -> (nat : Nat) -> Type where
  MkFinToNat : FinToNat fin (finToNat fin)

finToNat : (fin : Fin ub) -> Subset Nat (FinToNat fin)
finToNat fin = Element (Fin.finToNat fin) MkFinToNat

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_FinToNat_injective : (fin : Fin ub)
                        -> (n,m : Nat)
                        -> (p : FinToNat fin n)
                        -> (q : FinToNat fin m)
                        -> n = m
lemma_FinToNat_injective fin (finToNat fin) (finToNat fin) MkFinToNat MkFinToNat = Refl

lemma_FinToNat_singleton : (fin : Fin ub) -> (nat : Nat) -> (p,q : FinToNat fin nat) -> p = q
lemma_FinToNat_singleton fin (finToNat fin) MkFinToNat MkFinToNat = Refl