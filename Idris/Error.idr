module Error

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| An error type for convenience. The error can either contain an error message or some value
||| given some type of that value.
|||
||| For when the need of a proof is absent.
public export
data Error : Type where
  StdErr : String -> Error
  TyErr : {ty : Type} -> (x : ty) -> Error

||| A Maybe/Either convenience type for Error.
public export
data ErrorOr : Type -> Type where
  Err : Error -> ErrorOr ty
  Just : (x : ty) -> ErrorOr ty

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Functor ErrorOr where
  map f (Err err) = Err err
  map f (Just x) = Just (f x)

export 
implementation Show Error where
  show (StdErr err) = err
  show (TyErr x) = "TyErr"

export
implementation Show c => Show (ErrorOr c) where
  show (Err err) = show err
  show (Just x)  = show x