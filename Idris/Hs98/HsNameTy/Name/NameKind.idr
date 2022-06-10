module Hs98.HsNameTy.NameKind

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| We are concerned with names for variables and constructors.
data HsNameKind : Type where
  Variable    : HsNameKind
  Constructor : HsNameKind

