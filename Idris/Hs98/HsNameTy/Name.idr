module Hs98.NameTy.Name

import IdrisUtils.Utils
import IdrisUtils.Char.Char
import IdrisUtils.Ord

import public Hs98.HsNameTy.Name.NameKind
import public Hs98.HsNameTy.Name.NameDef

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [ValidHsNameChar] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Utilities] ------------------------------------------------------------------------------------

decValidHsNameChar_invalid : {x : Char.Char}
                          -> (npri : Not (Prime x))
                          -> (nnum : Not (Numeral x))
                          -> (nmaj : Not (Majuscule x))
                          -> (nmin : Not (Minuscule x))
                          -> ValidHsNameChar x
                          -> Void
decValidHsNameChar_invalid npri nnum nmaj nmin (Min ok) = nmin ok
decValidHsNameChar_invalid npri nnum nmaj nmin (Maj ok) = nmaj ok
decValidHsNameChar_invalid npri nnum nmaj nmin (Num ok) = nnum ok
decValidHsNameChar_invalid npri nnum nmaj nmin (Pri ok) = npri ok

-- [Decision Procedure] ---------------------------------------------------------------------------

decValidHsNameChar : (x : Char.Char) -> Dec (ValidHsNameChar x)
decValidHsNameChar x with (isMinuscule x)
  | Yes min = Yes (Min min)
  | No nmin with (isMajuscule x)
    | Yes maj = Yes (Maj maj)
    | No nmaj with (isNumeral x)
      | Yes num = Yes (Num num)
      | No nnum with (isPrime x)
        | Yes pri = Yes (Pri pri)
        | No npri = No (decValidHsNameChar_invalid npri nnum nmaj nmin)

-- [Properties] -----------------------------------------------------------------------------------

lemma_ValidHsNameChar_singletonImp : (p, q : ValidHsNameChar x) -> p = q
lemma_ValidHsNameChar_singletonImp (Min p) (Min q) =
  case lemma_Minuscule_singleton p q of Refl => Refl
lemma_ValidHsNameChar_singletonImp (Maj p) (Maj q) =
  case lemma_Majuscule_singleton p q of Refl => Refl
lemma_ValidHsNameChar_singletonImp (Num p) (Num q) =
  case lemma_Numeral_singleton p q of Refl => Refl
lemma_ValidHsNameChar_singletonImp (Pri p) (Pri q) =
  case lemma_Prime_singleton p q of Refl => Refl
lemma_ValidHsNameChar_singletonImp (Maj IsMaj1st) (Min _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj2nd) (Min _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj3rd) (Min _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj1st) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj2nd) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj3rd) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj1st) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj2nd) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Maj IsMaj3rd) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsUndscr) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin1st) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin2nd) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin3rd) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsUndscr) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin1st) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin2nd) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin3rd) (NameDef.Num _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsUndscr) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin1st) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin2nd) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Min IsMin3rd) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (NameDef.Num IsNum) (Min _) impossible
lemma_ValidHsNameChar_singletonImp (NameDef.Num IsNum) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (NameDef.Num IsNum) (Pri _) impossible
lemma_ValidHsNameChar_singletonImp (Pri IsPri) (Min _) impossible
lemma_ValidHsNameChar_singletonImp (Pri IsPri) (Maj _) impossible
lemma_ValidHsNameChar_singletonImp (Pri IsPri) (NameDef.Num _) impossible

lemma_ValidHsNameChar_singleton : (x : Char.Char) -> (p, q : ValidHsNameChar x) -> p = q
lemma_ValidHsNameChar_singleton x p q = lemma_ValidHsNameChar_singletonImp p q

---------------------------------------------------------------------------------------------------
-- [NotReserved] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Decision Procedure] --------------------------------------------------------------------------

isNotReserved : (s : Str) -> Dec (NotReserved s)
isNotReserved s with (isNotElem TotalOrderingStr s NameDef.reserved)
  | No  rv = No (\(MkNotReserved ok) => rv ok)
  | Yes ok = Yes (MkNotReserved ok)

-- [DecEq] ----------------------------------------------------------------------------------------

{-
decEqNRev_neq : (neq : Not (fs_p = fs_q))
             -> (MkNotReserved {fs=fs_p} p = MkNotReserved {fs=fs_q} q)
             -> Void
decEqNRev_neq neq Refl = neq Refl

||| Can't define a singleton lemma for two instances of two instances of NotReserved that are
||| indexed by the same string because it has a NotElem proof, which itself isn't injective.
|||
||| Unless, I suppose you extend it with a thing that tells you what the fs are exactly for xs...
||| TODO: Try this after you've got the simpler decEq version working.
||| Yes, you make the xs-fs relations a singleton itself.
decEqNRev : (p,q : NotReserved x) -> Dec (p = q)
decEqNRev {x} (MkNotReserved {fs=fs_p} p) (MkNotReserved {fs=fs_q} q) =
  case decEq fs_p fs_q of
    No neq => No (decEqNRev_neq neq)
    Yes Refl =>
      case lemma_NotElem_singleton TotalOrderingStr x reserved fs_p p q of Refl => Yes Refl
-}

lemma_NotReserved_singleton : (p,q : NotReserved s) -> p = q
lemma_NotReserved_singleton {s} (MkNotReserved p) (MkNotReserved q) =
  cong (lemma_NotElem_singleton TotalOrderingStr s NameDef.reserved p q)

---------------------------------------------------------------------------------------------------
-- [RStrName] -------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

emptyStrNotValidName : Subset (Name k) (RStrName (MkStr []) k) -> Void
emptyStrNotValidName (Element _ RHsVar) impossible
emptyStrNotValidName (Element _ RHsCtr) impossible

strAsVariable : (s : Str) -> Dec (Subset (Name Variable) (RStrName s Variable))
strAsVariable (MkStr []) = No emptyStrNotValidName
strAsVariable (MkStr (x :: xs)) with (isNotReserved (MkStr (x :: xs)))
  | No nok_rv = No (\(Element (HsVarName (MkStr (x :: xs))) (RHsVar {ok_rv})) => nok_rv ok_rv)
  | Yes ok_rv with (isMinuscule x)
    | No nok_hd = No (\(Element (HsVarName (MkStr (x :: xs))) (RHsVar {ok_hd})) => nok_hd ok_hd)
    | Yes ok_hd with (decAll decValidHsNameChar xs)
      | No nok_tl = No (\(Element (HsVarName (MkStr (x :: xs))) (RHsVar {ok_tl})) => nok_tl ok_tl)
      | Yes ok_tl = Yes (Element (HsVarName (MkStr (x :: xs)))
                                 (RHsVar {ok_hd = ok_hd} {ok_tl = ok_tl} {ok_rv = ok_rv}))

strAsConstructor : (s : Str) -> Dec (Subset (Name Constructor) (RStrName s Constructor))
strAsConstructor (MkStr []) = No emptyStrNotValidName
strAsConstructor (MkStr (x :: xs)) with (isMajuscule x)
  | No nok_hd = No (\(Element (HsCtrName (MkStr (x :: xs))) (RHsCtr {ok_hd})) => nok_hd ok_hd)
  | Yes ok_hd with (decAll decValidHsNameChar xs)
    | No nok_tl = No (\(Element (HsCtrName (MkStr (x :: xs))) (RHsCtr {ok_tl})) => nok_tl ok_tl)
    | Yes ok_tl = Yes (Element (HsCtrName (MkStr (x :: xs)))
                               (RHsCtr {ok_hd = ok_hd} {ok_tl = ok_tl}))

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Equality.DecEq (Name k) where
  decEq (HsVarName (MkStr {strlen = S n} (x :: xs))
                   {s_cns = MkStrSplit} {ok_hd = p1} {ok_tl = p2} {ok_rv = p3}) 
        (HsVarName (MkStr {strlen = S m} (y :: ys))
                   {s_cns = MkStrSplit} {ok_hd = q1} {ok_tl = q2} {ok_rv = q3}) =
    case decEq (MkStr {strlen = S n} (x :: xs)) (MkStr {strlen = S m} (y :: ys)) of
      No  neq  => No (\Refl => neq Refl)
      Yes Refl =>
        case (lemma_Minuscule_singleton p1 q1,
              lemma_All_singleton lemma_ValidHsNameChar_singleton p2 q2,
              lemma_NotReserved_singleton p3 q3) of
          (Refl, Refl, Refl) => Yes Refl
  decEq (HsCtrName (MkStr {strlen = S n} (x :: xs))
                    {s_cns = MkStrSplit} {ok_hd = p1} {ok_tl = p2})
        (HsCtrName (MkStr {strlen = S m} (y :: ys))
                    {s_cns = MkStrSplit} {ok_hd = q1} {ok_tl = q2}) =
    case decEq (MkStr {strlen = S n} (x :: xs)) (MkStr {strlen = S m} (y :: ys)) of
      No  neq  => No (\Refl => neq Refl)
      Yes Refl =>
        case (lemma_Majuscule_singleton p1 q1,
              lemma_All_singleton lemma_ValidHsNameChar_singleton p2 q2) of
          (Refl, Refl) => Yes Refl

---------------------------------------------------------------------------------------------------
-- [Convenience Functions] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- Would mark myself down for duplicate code here...
testStringPairToValidName : (s1,s2 : String)
                         -> (k : HsNameKind)
                         -> Either (String, (c : Type ** c))
                                   (x : Name k ** y : Name k ** Dec (x = y))
testStringPairToValidName s1 s2 Constructor =
  case (fromString s1, fromString s2) of
    (Just s1', Just s2') =>
      case (strAsConstructor s1') of
        No p => Left ("s1 not a valid constructor name",
                      (Not (Subset (Name Constructor) (RStrName s1' Constructor)) ** p))
        Yes (Element x p) =>
          case strAsConstructor s2' of
            No p => Left ("s2 not a valid constructor name",
                          (Not (Subset (Name Constructor) (RStrName s2' Constructor)) ** p))
            Yes (Element y q) => Right (x ** y ** decEq x y)
    (Nothing, Just _)  => Left ("s1 has unexpected characters", (() ** ()))
    (Just _,  Nothing) => Left ("s2 has unexpected characters", (() ** ()))
    (Nothing, Nothing) => Left ("both s1 and s2 have unexpected characters", (() ** ()))
testStringPairToValidName s1 s2 Variable =
  case (fromString s1, fromString s2) of
    (Just s1', Just s2') =>
      case (strAsVariable s1') of
        No p => Left ("s1 not a valid variable name",
                      (Not (Subset (Name Variable) (RStrName s1' Variable)) ** p))
        Yes (Element x p) =>
          case strAsVariable s2' of
            No p => Left ("s2 not a valid variable name",
                          (Not (Subset (Name Variable) (RStrName s2' Variable)) ** p))
            Yes (Element y q) => Right (x ** y ** decEq x y)
    (Nothing, Just _)  => Left ("s1 has unexpected characters", (() ** ()))
    (Just _,  Nothing) => Left ("s2 has unexpected characters", (() ** ()))
    (Nothing, Nothing) => Left ("both s1 and s2 have unexpected characters", (() ** ()))

---------------------------------------------------------------------------------------------------
-- [Total Order Over Variable Names] --------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTVarName : Name Variable -> Name Variable -> Type where
  IsLTVarName : (lt : LTStr x y) -> LTVarName (HsVarName x) (HsVarName y)

isLTVarName : (x,y : Name Variable) -> Dec (LTVarName x y)
isLTVarName (HsVarName x) (HsVarName y) with (isLTStr x y)
  | No gte = No (\(IsLTVarName lt) => gte lt)
  | Yes lt = Yes (IsLTVarName lt)

singLTVarName : (x,y : Name Variable) -> (p,q : LTVarName x y) -> p = q
singLTVarName (HsVarName x) (HsVarName y) (IsLTVarName p) (IsLTVarName q) =
  case singLTStr x y p q of
    Refl => Refl

irreflLTVarName : (x : Name Variable) -> (p : LTVarName x x) -> Void
irreflLTVarName (HsVarName x) (IsLTVarName lt) = irreflLTStr x lt

antisymLTVarName : (x, y : Name Variable) -> (p : LTVarName x y) -> (q : LTVarName y x) -> Void
antisymLTVarName (HsVarName x) (HsVarName y) (IsLTVarName p) (IsLTVarName q) =
  antisymLTStr x y p q

TotalOrderingVarName : TotalOrdering (Name Variable)
TotalOrderingVarName =
  MkTotOrd LTVarName isLTVarName singLTVarName irreflLTVarName antisymLTVarName decEq
