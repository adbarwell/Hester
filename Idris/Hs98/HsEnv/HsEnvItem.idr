module Hs98.HsEnv.HsEnvItem

import IdrisUtils.Utils
import IdrisUtils.Ord
import Hs98.HsNameTy

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data EnvItem : HsNameKind -> Type where
  MkEnvItem : (id : Nat) -> (na : Name k) -> EnvItem k

---------------------------------------------------------------------------------------------------
-- [Relations] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data EnvItemId : (ei : EnvItem k) -> (id : Nat) -> Type where
  MkEnvItemId : EnvItemId (MkEnvItem id na) id

getEnvItemId : (ei : EnvItem k) -> Subset Nat (EnvItemId ei)
getEnvItemId (MkEnvItem id na) = Element id MkEnvItemId

lemma_EnvItemId_injective : (x : EnvItem k)
                         -> (y : Nat)
                         -> (z : Nat)
                         -> (p : EnvItemId x y)
                         -> (q : EnvItemId x z)
                         -> y = z
lemma_EnvItemId_injective (MkEnvItem id na) id id MkEnvItemId MkEnvItemId = Refl

lemma_EnvItemId_singleton : (x : EnvItem k)
                         -> (y : Nat)
                         -> (p : EnvItemId x y)
                         -> (q : EnvItemId x y)
                         -> p = q
lemma_EnvItemId_singleton (MkEnvItem id na) id MkEnvItemId MkEnvItemId = Refl

data EnvItemNa : (ei : EnvItem k) -> (name : Name k) -> Type where
  MkEnvItemNa : EnvItemNa (MkEnvItem id na) na

getEnvItemNa : (ei : EnvItem k) -> Subset (Name k) (EnvItemNa ei)
getEnvItemNa (MkEnvItem id na) = Element na MkEnvItemNa

lemma_EnvItemNa_injective : (x : EnvItem k)
                         -> (y : Name k)
                         -> (z : Name k)
                         -> (p : EnvItemNa x y)
                         -> (q : EnvItemNa x z)
                         -> y = z
lemma_EnvItemNa_injective (MkEnvItem id na) na na MkEnvItemNa MkEnvItemNa = Refl

lemma_EnvItemNa_singleton : (x : EnvItem k) -> (y : Name k) -> (p,q : EnvItemNa x y) -> p = q
lemma_EnvItemNa_singleton (MkEnvItem id na) na MkEnvItemNa MkEnvItemNa = Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Equality.DecEq (EnvItem k) where
  decEq (MkEnvItem id1 na1) (MkEnvItem id2 na2) with (decEq id1 id2)
    decEq (MkEnvItem id1 na1) (MkEnvItem id2 na2) | No neq_id = No (\Refl => neq_id Refl)
    decEq (MkEnvItem id2 na1) (MkEnvItem id2 na2) | Yes Refl with (decEq na1 na2)
      decEq (MkEnvItem id2 na1) (MkEnvItem id2 na2) | Yes Refl | No neq_na =
        No (\Refl => neq_na Refl)
      decEq (MkEnvItem id2 na2) (MkEnvItem id2 na2) | Yes Refl | Yes Refl =
        Yes Refl
