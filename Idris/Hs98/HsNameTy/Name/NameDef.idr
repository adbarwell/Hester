module Hs98.NameTy.Name.NameDef

import IdrisUtils.Utils
import IdrisUtils.Char.Char
import IdrisUtils.Ord

import Hs98.HsNameTy.Name.NameKind

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Valid Characters in a Name] -------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A valid variable/constructor name is made up from valid characters.
|||
||| We use 'name' instead of 'identifier' to avoid confusion since we're extending 'identifiers' 
||| (names) with (unique) identifiers (natural numbers).
|||
||| From the Haskell98 Report:
|||
||| > An identifier consists of a letter followed by zero or more letters, digits, underscores,
||| > and single quotes.
data ValidHsNameChar : Char.Char -> Type where
  Min : Minuscule x -> ValidHsNameChar x
  Maj : Majuscule x -> ValidHsNameChar x
  Num : Numeral   x -> ValidHsNameChar x
  Pri : Prime     x -> ValidHsNameChar x

||| A vector of reserved names. (Not to be used as variable names.)
|||
||| From the Haskell98 Report, these include:
|||
||| > case, class, data, default, deriving, do, else,	if, import, in, infix, infixl, infixr,
||| > instance, let, module, newtype, of, then, type, where, _
reserved : Vect 22 Str
reserved = [MkStr [MkChar Cc, MkChar Ca, MkChar Cs, MkChar Ce],
            MkStr [MkChar Cc, MkChar Cl, MkChar Ca, MkChar Cs, MkChar Cs],
            MkStr [MkChar Cd, MkChar Ca, MkChar Ct, MkChar Ca],
            MkStr [MkChar Cd, MkChar Ce, MkChar Cf, MkChar Ca, MkChar Cu, MkChar Cl, MkChar Ct],
            MkStr [MkChar Cd, MkChar Ce, MkChar Cr, MkChar Ci, MkChar Cv, MkChar Ci, MkChar Cn, MkChar Cg],
            MkStr [MkChar Cd, MkChar Co],
            MkStr [MkChar Ce, MkChar Cl, MkChar Cs, MkChar Ce],
            MkStr [MkChar Ci, MkChar Cf],
            MkStr [MkChar Ci, MkChar Cm, MkChar Cp, MkChar Co, MkChar Cr, MkChar Ct],
            MkStr [MkChar Ci, MkChar Cn],
            MkStr [MkChar Ci, MkChar Cn, MkChar Cf, MkChar Ci, MkChar Cx],
            MkStr [MkChar Ci, MkChar Cn, MkChar Cf, MkChar Ci, MkChar Cx, MkChar Cl],
            MkStr [MkChar Ci, MkChar Cn, MkChar Cf, MkChar Ci, MkChar Cx, MkChar Cr],
            MkStr [MkChar Ci, MkChar Cn, MkChar Cs, MkChar Ct, MkChar Ca, MkChar Cn, MkChar Cc, MkChar Ce],
            MkStr [MkChar Cl, MkChar Ce, MkChar Ct],
            MkStr [MkChar Cm, MkChar Co, MkChar Cd, MkChar Cu, MkChar Cl, MkChar Ce],
            MkStr [MkChar Cn, MkChar Ce, MkChar Cw, MkChar Ct, MkChar Cy, MkChar Cp, MkChar Ce],
            MkStr [MkChar Co, MkChar Cf],
            MkStr [MkChar Ct, MkChar Ch, MkChar Ce, MkChar Cn],
            MkStr [MkChar Ct, MkChar Cy, MkChar Cp, MkChar Ce],
            MkStr [MkChar Cw, MkChar Ch, MkChar Ce, MkChar Cr, MkChar Ce],
            MkStr [MkChar C_]]

||| Proof that some string is not in the reserved keywords list.
||| 
||| N.B. Includes the wildcard by itself; wildcards in patterns are treated at the pattern level.
data NotReserved : (s : Str) -> Type where
  MkNotReserved : (ok : NotElem TotalOrderingStr s NameDef.reserved) -> NotReserved s

---------------------------------------------------------------------------------------------------
-- [Name Definition] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A representation of a valid Haskell 98 name.
||| 
||| We use 'name' instead of 'identifier' to avoid confusion since we're extending 'identifiers' 
||| (names) with (unique) identifiers (natural numbers).
|||
||| The proofs of well-formedness (i.e. `ok_hd`, `ok_tl`, and `ok_rv`) are *implicit* in order to
||| avoid having as part of the visible AST (e.g. in the REPL) and in order to promote their
||| erasure (since I don't envisage that we're going to use them as part of a refactoring).
data Name : HsNameKind -> Type where
  ||| What is in a Variable Name?
  |||
  ||| @s_cns  the string should not be empty.
  ||| @ok_hd  the first character should either be an underscore or a lower-case letter.
  ||| @ok_tl  the remaining characters should be alphanumeric, an underscore, or a tick.
  ||| @ok_rv  the name should not be reserved.
  HsVarName : (s     : Str)
           -> {s_cns : StrSplit s s_hd s_tl}
           -> {ok_hd : Minuscule s_hd}
           -> {ok_tl : All ValidHsNameChar s_tl}
           -> {ok_rv : NotReserved s}
           -> Name Variable
  ||| A Constructor by any other Name would smell as sweet.
  |||
  ||| @s_cns  the string should not be empty.
  ||| @ok_hd  the first character should be an upper-case letter.
  ||| @ok_tl  the remaining characters should be alphanumeric, an underscore, or a tick.
  HsCtrName : (s     : Str)
           -> {s_cns : StrSplit s s_hd s_tl}
           -> {ok_hd : Majuscule s_hd}
           -> {ok_tl : All ValidHsNameChar s_tl}
           -> Name Constructor

---------------------------------------------------------------------------------------------------
-- [Name Construction Relation] -------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that a string is a valid variable or constructor name.
data RStrName : (s : Str) -> (k : HsNameKind) -> (na : Name k) -> Type where
  RHsVar : {ok_hd : Minuscule x}
        -> {ok_tl : All ValidHsNameChar xs}
        -> {ok_rv : NotReserved (MkStr (x :: xs))}
        -> RStrName (MkStr (x :: xs))
                    Variable
                    (HsVarName (MkStr (x :: xs))
                               {s_cns = MkStrSplit} {ok_hd = ok_hd} {ok_tl = ok_tl} {ok_rv = ok_rv})
  RHsCtr : {ok_hd : Majuscule x}
        -> {ok_tl : All ValidHsNameChar xs}
        -> RStrName (MkStr (x :: xs))
                    Constructor
                    (HsCtrName (MkStr (x :: xs))
                               {s_cns = MkStrSplit} {ok_hd = ok_hd} {ok_tl = ok_tl})

