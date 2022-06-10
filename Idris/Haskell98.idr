||| Taken & adapted from Language.Haskell.Syntax (haskell-src-1.0.3.1 on Hackage)
module Haskell98

%default total
%access public export

{-
data Rational : Type where
  MkRational : Int -> Int -> Rational
-}

data SrcLocTy : Type where
  SrcLoc : String -> Nat -> Nat -> SrcLocTy

data ModuleTy : Type where
  Module : (name : String) -> ModuleTy

data HsNameTy : Type where
  HsIdent  : String -> HsNameTy
  HsSymbol : String -> HsNameTy

data HsSpecialConTy : Type where
  -- ||| unit type and data constructor ()
  -- HsUnitCon : HsSpecialConTy
  -- ||| list type constructor []
  -- HsListCon : HsSpecialConTy
  -- ||| function type constructor ->
  -- HsFunCon : HsSpecialConTy
  -- ||| /n/-ary tuple type and data --   constructors (,) etc
  -- HsTupleCon : Int -> HsSpecialConTy
  ||| list data constructor (:)
  HsCons : HsSpecialConTy

{-
data HsGuardedRhsTy : Type where
-}

{-
data HsPatField : Type where
-}

data HsQNameTy : Type where
  -- ||| name qualified with a module name
  -- Qual : ModuleTy -> HsNameTy -> HsQNameTy
  ||| unqualified name
  UnQual : HsNameTy -> HsQNameTy
  ||| built-in constructor with special syntax
  Special : HsSpecialConTy -> HsQNameTy

data HsLiteralTy : Type where
  -- ||| character literal
  -- HsChar :        Char -> HsLiteralTy
  -- ||| string literal
  -- HsString :      String -> HsLiteralTy
  ||| integer literal
  HsInt : Integer -> HsLiteralTy
  -- ||| floating point literal
  -- HsFrac :        Rational -> HsLiteralTy
  -- ||| GHC unboxed character literal
  -- HsCharPrim :    Char -> HsLiteralTy
  -- ||| GHC unboxed string literal
  -- HsStringPrim :  String -> HsLiteralTy
  -- ||| GHC unboxed integer literal
  -- HsIntPrim :     Integer -> HsLiteralTy
  -- ||| GHC unboxed float literal
  -- HsFloatPrim :   Rational -> HsLiteralTy
  -- ||| GHC unboxed double literal
  -- HsDoublePrim :  Rational -> HsLiteralTy

{-
data HsSafetyTy : Type where

data HsOpTy : Type where

data HsAssocTy : Type where

data HsConDeclTy : Type where

data HsContextTy : Type where

data HsTypeTy : Type where

data HsQualTypeTy : Type where

data HsFieldUpdateTy : Type where
-}

data HsQOpTy : Type where
  ||| variable operator (/qvarop/)
  HsQVarOp : HsQNameTy -> HsQOpTy
  -- ||| constructor operator (/qconop/)
  -- HsQConOp : HsQNameTy -> HsQOpTy

{-
data HsStmtTy : Type where

-}

mutual
  data HsGuardedAltsTy : Type where
    HsUnGuardedAlt : (e : HsExpTy) -> HsGuardedAltsTy
    -- HsGuardedAlts  : (gs : List HsGuardedAlt) -> HsGuardedAltsTy


  data HsAltTy : Type where
    HsAlt : (loc : SrcLocTy)
         -> (p : HsPatTy)
         -> (rhs : HsGuardedAltsTy)
         -> (wheres : List HsDeclTy)
         -> HsAltTy

  data HsMatchTy : Type where
    HsMatch : (loc : SrcLocTy)
           -> (fname : HsNameTy)
           -> (pats : List HsPatTy)
           -> (rhs : HsRhsTy)
           -> (wheres : List HsDeclTy)
           -> HsMatchTy

  data HsDeclTy : Type where
    ||| Collects a list of contiguous matches with the same function name.
    ||| e.g.
    ||| ```
    ||| f x = ...
    ||| f y = ...
    ||| ```
    ||| will result in a single `HsFunBind` constructor in a `HsModule`
    |||
    ||| Note that it is possible to have another FunBind later in a HsModuleTy with the *same* name
    ||| when a match with a different name occurs in between.
    ||| e.g.
    ||| ```
    ||| f x = ...
    ||| g y = ...
    ||| f z = ...
    ||| ```
    ||| will lead to *three* `HsFunBind` constructors in a `HsModule`.
    HsFunBind       : (matches : List HsMatchTy) -> HsDeclTy
    HsPatBind       : (loc : SrcLocTy) -> (p : HsPatTy) -> (rhs : HsRhsTy)
                   -> (wheres : List HsDeclTy) -> HsDeclTy

    -- HsTypeDecl      : (loc : SrcLocTy) -> HsNameTy -> List HsNameTy -> HsTypeTy -> HsDeclTy
    -- HsDataDecl      : (loc : SrcLocTy) -> HsContextTy -> HsNameTy -> List HsNameTy
    --                -> List HsConDeclTy -> HsQNameTy -> HsDeclTy
    -- HsInfixDecl     : (loc : SrcLocTy) -> HsAssocTy -> Int -> List HsOpTy -> HsDeclTy
    -- HsNewTypeDecl   : (loc : SrcLocTy) -> HsContextTy -> HsNameTy -> List HsNameTy
    --                -> HsConDeclTy -> List HsQNameTy -> HsDeclTy
    -- HsClassDecl     : (loc : SrcLocTy) -> HsContextTy -> HsNameTy -> List HsNameTy
    --                -> List HsDeclTy -> HsDeclTy
    -- HsInstDecl      : (loc : SrcLocTy) -> HsContextTy -> HsQNameTy -> List HsTypeTy
    --                -> List HsDeclTy -> HsDeclTy
    -- HsDefaultDecl   : (loc : SrcLocTy) -> List HsTypeTy -> HsDeclTy
    -- HsTypeSig       : (loc : SrcLocTy) -> List HsNameTy -> HsQualTypeTy -> HsDeclTy
    -- HsForeignImport : (loc : SrcLocTy) -> String -> HsSafetyTy -> String -> HsNameTy
    --                -> HsTypeTy -> HsDeclTy
    -- HsForeignExport : (loc : SrcLocTy) -> String -> String -> HsNameTy -> HsTypeTy -> HsDeclTy

  data HsExpTy : Type where
    ||| variable
    HsVar : HsQNameTy                 -> HsExpTy
    -- ||| data constructor
    -- HsCon : HsQNameTy                 -> HsExpTy
    ||| literal constant
    HsLit : HsLiteralTy               -> HsExpTy
    ||| infix application
    HsInfixApp : HsExpTy -> HsQOpTy -> HsExpTy  -> HsExpTy
    ||| ordinary application
    HsApp : HsExpTy -> HsExpTy             -> HsExpTy
    -- ||| negation expression - /exp/
    -- HsNegApp : HsExpTy                -> HsExpTy
    ||| lambda expression
    HsLambda : SrcLocTy -> List HsPatTy -> HsExpTy -> HsExpTy
    -- ||| local declarations with let
    -- HsLet : List HsDeclTy -> HsExpTy          -> HsExpTy
    -- ||| if /exp/ then /exp/ else /exp/
    -- HsIf : HsExpTy -> HsExpTy -> HsExpTy        -> HsExpTy
    ||| case /exp/ of /alts/
    HsCase : HsExpTy -> List HsAltTy          -> HsExpTy
    -- ||| do-expression: -- the last statement in the list -- should be an expression.
    -- HsDo : List HsStmtTy                 -> HsExpTy
    -- ||| tuple expression
    -- HsTuple : List HsExpTy               -> HsExpTy
    -- ||| list expression
    -- HsList : List HsExpTy                -> HsExpTy
    ||| parenthesized expression
    HsParen : HsExpTy                 -> HsExpTy
    -- ||| left section (/exp/ /qop/)
    -- HsLeftSection : HsExpTy -> HsQOpTy     -> HsExpTy
    -- ||| right section (/qop/ /exp/)
    -- HsRightSection : HsQOpTy -> HsExpTy    -> HsExpTy
    -- ||| record construction expression
    -- HsRecConstr : HsQNameTy -> List HsFieldUpdateTy -> HsExpTy
    -- ||| record update expression
    -- HsRecUpdate : HsExpTy -> List HsFieldUpdateTy -> HsExpTy
    -- ||| unbounded arithmetic sequence, -- incrementing by 1
    -- HsEnumFrom : HsExpTy              -> HsExpTy
    -- ||| bounded arithmetic sequence, -- incrementing by 1
    -- HsEnumFromTo : HsExpTy -> HsExpTy      -> HsExpTy
    -- ||| unbounded arithmetic sequence, -- with first two elements given
    -- HsEnumFromThen : HsExpTy -> HsExpTy    -> HsExpTy
    -- ||| bounded arithmetic sequence, -- with first two elements given
    -- HsEnumFromThenTo : HsExpTy -> HsExpTy -> HsExpTy -> HsExpTy
    -- ||| list comprehension
    -- HsListComp : HsExpTy -> List HsStmtTy     -> HsExpTy
    -- ||| expression type signature
    -- HsExpTypeSig : SrcLocTy -> HsExpTy -> HsQualTypeTy -> HsExpTy
    -- ||| patterns only
    -- HsAsPat : HsNameTy -> HsExpTy          -> HsExpTy
    -- ||| patterns only
    -- HsWildCard : HsExpTy
    -- ||| patterns only
    -- HsIrrPat : HsExpTy                -> HsExpTy

  data HsRhsTy : Type where
    HsUnGuardedRhs : (e : HsExpTy) ->  HsRhsTy
    -- HsGuardedRhss : List HsGuardedRhsTy -> HsRhsTy

  data HsPatTy : Type where
    ||| variable
    HsPVar : (name : HsNameTy) -> HsPatTy
    -- ||| literal constant
    -- HsPLit : (lit : HsLiteralTy) -> HsPatTy
    -- ||| negated pattern
    -- HsPNeg : (p : HsPatTy) -> HsPatTy
    ||| pattern with infix data constructor
    HsPInfixApp : (p1 : HsPatTy) -> (op : HsQNameTy) -> (p2 : HsPatTy) -> HsPatTy 
    ||| data constructor and argument patterns
    HsPApp : (c : HsQNameTy) -> (args : List HsPatTy) -> HsPatTy
    -- ||| tuple pattern
    -- HsPTuple : (ps : List HsPatTy) -> HsPatTy 
    ||| list pattern
    HsPList : (ps : List HsPatTy) -> HsPatTy 
    -- ||| parenthesized pattern
    HsPParen : (p : HsPatTy) -> HsPatTy 
    -- -- ||| labelled pattern
    -- -- HsPRec : HsQNameTy -> List HsPatTyField -> HsPatTy
    -- ||| \@-pattern
    -- HsPAsPat : (name : HsNameTy) -> (p : HsPatTy) -> HsPatTy
    -- ||| wildcard pattern (_)
    -- HsPWildCard : HsPatTy
    -- ||| irrefutable pattern (~)
    -- HsPIrrPat : (p : HsPatTy) -> HsPatTy

data HsExportSpec : Type where

data HsImportSpecTy : Type where
  -- HsIVar : HsNameTy -> HsImportSpecTy

data HsImportDeclTy : Type where
  -- HsImportDecl : SrcLocTy -> ModuleTy -> Bool -> Maybe ModuleTy -> Maybe (Bool, List HsImportSpecTy) -> HsImportDeclTy

data HsModuleTy : Type where
  HsModule : (loc : SrcLocTy)
          -> (mname : ModuleTy)
          -> (exports : Maybe (List HsExportSpec))
          -> (imports : List HsImportDeclTy)
          -> (decls : List HsDeclTy)
          -> HsModuleTy

-- [Implementations] ------------------------------------------------------------------------------

implementation Uninhabited (HsIdent x = HsSymbol y) where
  uninhabited Refl impossible
implementation Uninhabited (HsSymbol x = HsIdent y) where
  uninhabited Refl impossible

implementation DecEq HsNameTy where
  decEq (HsIdent x) (HsIdent y) with (decEq x y)
    decEq (HsIdent y) (HsIdent y) | Yes Refl = Yes Refl
    decEq (HsIdent x) (HsIdent y) | No c = No (\Refl => c Refl)
  decEq (HsSymbol x) (HsSymbol y) with (decEq x y)
    decEq (HsSymbol y) (HsSymbol y) | Yes Refl = Yes Refl
    decEq (HsSymbol x) (HsSymbol y) | No c = No (\Refl => c Refl)
  decEq (HsIdent x) (HsSymbol y) = No absurd
  decEq (HsSymbol x) (HsIdent y) = No absurd

implementation Eq HsNameTy where
  (==) (HsIdent x) (HsIdent y) = x == y
  (==) (HsIdent x) (HsSymbol y) = False
  (==) (HsSymbol x) (HsIdent y) = False
  (==) (HsSymbol x) (HsSymbol y) = x == y
