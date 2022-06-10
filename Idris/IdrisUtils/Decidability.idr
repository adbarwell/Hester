module IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Proposition] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Prop : Type where
  |||
  ||| @p        some type
  ||| @q        the inverse of `p`
  ||| @isP      decision procedure for `p`
  ||| @isQ      decision procedure for `q`
  ||| @p_sound  a proof that `p -> ¬q`
  ||| @q_sound  a proof that `q -> ¬p`
  MkProp : (p       : Type)
        -> (q       : Type)
        -> (isP     : Dec p)
        -> (isQ     : Dec q)
        -> (p_sound : p -> Not q)
        -> (q_sound : q -> Not p)
        -> Prop

proj_P : Prop -> Type
proj_P (MkProp p q isP isQ p_sound q_sound) = p

proj_Q : Prop -> Type
proj_Q (MkProp p q isP isQ p_sound q_sound) = q

proj_isP : (pred : Prop) -> Dec (proj_P pred)
proj_isP (MkProp p q isP isQ p_sound q_sound) = isP

proj_isQ : (pred : Prop) -> Dec (proj_Q pred)
proj_isQ (MkProp p q isP isQ p_sound q_sound) = isQ

proj_P_sound : (pred : Prop) -> (prf : proj_P pred) -> Not (proj_Q pred)
proj_P_sound (MkProp p q isP isQ p_sound q_sound) = p_sound

proj_Q_sound : (pred : Prop) -> (prf : proj_Q pred) -> Not (proj_P pred)
proj_Q_sound (MkProp p q isP isQ p_sound q_sound) = q_sound

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A pecidable property `p` either holds or its inverse property `q` holds.
data Dec : (pred : Prop) -> Type where
  Yes : (prf : proj_P pred) -> Dec pred
  No  : (contra : proj_Q pred) -> Dec pred

||| A property is decidable and has a decision procedure.
data Decidable : (pred : Prop) -> Type where
  IsDecidable : (decP : Dec pred) -> Decidable pred

decP : (dec : Decidable pred) -> Dec pred
decP (IsDecidable dec) = dec

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Dec_sound : Dec pred -> Basics.Dec (proj_P pred)
lemma_Dec_sound (Yes prf) = Yes prf
lemma_Dec_sound {pred} (No contra) = No (\prf => proj_Q_sound pred contra prf)
