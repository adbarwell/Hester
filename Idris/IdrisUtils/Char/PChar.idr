module IdrisUtils.Char.PChar

import IdrisUtils.Char.CharKind
import IdrisUtils.Nat

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Idris uses ASCII and that makes the natural numbers too large if you just `toNat` them.
|||
||| Let's try to be a bit more clever...
|||
||| The alternative is defining LT over Char pairwise which is going to be painful...
data PChar : Char -> (CharKind, Nat) -> Type where
  C_ : PChar '_' (Sym, 0)
  C' : PChar '\'' (Sym, 1)

  C0 : PChar '0' (Num, 0)
  C1 : PChar '1' (Num, 1)
  C2 : PChar '2' (Num, 2)
  C3 : PChar '3' (Num, 3)
  C4 : PChar '4' (Num, 4)
  C5 : PChar '5' (Num, 5)
  C6 : PChar '6' (Num, 6)
  C7 : PChar '7' (Num, 7)
  C8 : PChar '8' (Num, 8)
  C9 : PChar '9' (Num, 9)

  Ca : PChar 'a' (Min1st, 0)
  Cb : PChar 'b' (Min1st, 1)
  Cc : PChar 'c' (Min1st, 2)
  Cd : PChar 'd' (Min1st, 3)
  Ce : PChar 'e' (Min1st, 4)
  Cf : PChar 'f' (Min1st, 5)
  Cg : PChar 'g' (Min1st, 6)
  Ch : PChar 'h' (Min1st, 7)
  Ci : PChar 'i' (Min1st, 8)
  Cj : PChar 'j' (Min1st, 9)
  Ck : PChar 'k' (Min2nd, 0)
  Cl : PChar 'l' (Min2nd, 1)
  Cm : PChar 'm' (Min2nd, 2)
  Cn : PChar 'n' (Min2nd, 3)
  Co : PChar 'o' (Min2nd, 4)
  Cp : PChar 'p' (Min2nd, 5)
  Cq : PChar 'q' (Min2nd, 6)
  Cr : PChar 'r' (Min2nd, 7)
  Cs : PChar 's' (Min2nd, 8)
  Ct : PChar 't' (Min2nd, 9)
  Cu : PChar 'u' (Min3rd, 0)
  Cv : PChar 'v' (Min3rd, 1)
  Cw : PChar 'w' (Min3rd, 2)
  Cx : PChar 'x' (Min3rd, 3)
  Cy : PChar 'y' (Min3rd, 4)
  Cz : PChar 'z' (Min3rd, 5)

  CA : PChar 'A' (Maj1st, 0)
  CB : PChar 'B' (Maj1st, 1)
  CC : PChar 'C' (Maj1st, 2)
  CD : PChar 'D' (Maj1st, 3)
  CE : PChar 'E' (Maj1st, 4)
  CF : PChar 'F' (Maj1st, 5)
  CG : PChar 'G' (Maj1st, 6)
  CH : PChar 'H' (Maj1st, 7)
  CI : PChar 'I' (Maj1st, 8)
  CJ : PChar 'J' (Maj1st, 9)
  CK : PChar 'K' (Maj2nd, 0)
  CL : PChar 'L' (Maj2nd, 1)
  CM : PChar 'M' (Maj2nd, 2)
  CN : PChar 'N' (Maj2nd, 3)
  CO : PChar 'O' (Maj2nd, 4)
  CP : PChar 'P' (Maj2nd, 5)
  CQ : PChar 'Q' (Maj2nd, 6)
  CR : PChar 'R' (Maj2nd, 7)
  CS : PChar 'S' (Maj2nd, 8)
  CT : PChar 'T' (Maj2nd, 9)
  CU : PChar 'U' (Maj3rd, 0)
  CV : PChar 'V' (Maj3rd, 1)
  CW : PChar 'W' (Maj3rd, 2)
  CX : PChar 'X' (Maj3rd, 3)
  CY : PChar 'Y' (Maj3rd, 4)
  CZ : PChar 'Z' (Maj3rd, 5)

isPChar : (x : Char) -> Maybe (Subset (CharKind, Nat) (PChar x))
isPChar '_' = Just (Element (Sym, 0) C_)
isPChar '\'' = Just (Element (Sym, 1) C')
isPChar '0' = Just (Element (Num, 0) C0)
isPChar '1' = Just (Element (Num, 1) C1)
isPChar '2' = Just (Element (Num, 2) C2)
isPChar '3' = Just (Element (Num, 3) C3)
isPChar '4' = Just (Element (Num, 4) C4)
isPChar '5' = Just (Element (Num, 5) C5)
isPChar '6' = Just (Element (Num, 6) C6)
isPChar '7' = Just (Element (Num, 7) C7)
isPChar '8' = Just (Element (Num, 8) C8)
isPChar '9' = Just (Element (Num, 9) C9)
isPChar 'a' = Just (Element (Min1st, 0) Ca)
isPChar 'b' = Just (Element (Min1st, 1) Cb)
isPChar 'c' = Just (Element (Min1st, 2) Cc)
isPChar 'd' = Just (Element (Min1st, 3) Cd)
isPChar 'e' = Just (Element (Min1st, 4) Ce)
isPChar 'f' = Just (Element (Min1st, 5) Cf)
isPChar 'g' = Just (Element (Min1st, 6) Cg)
isPChar 'h' = Just (Element (Min1st, 7) Ch)
isPChar 'i' = Just (Element (Min1st, 8) Ci)
isPChar 'j' = Just (Element (Min1st, 9) Cj)
isPChar 'k' = Just (Element (Min2nd, 0) Ck)
isPChar 'l' = Just (Element (Min2nd, 1) Cl)
isPChar 'm' = Just (Element (Min2nd, 2) Cm)
isPChar 'n' = Just (Element (Min2nd, 3) Cn)
isPChar 'o' = Just (Element (Min2nd, 4) Co)
isPChar 'p' = Just (Element (Min2nd, 5) Cp)
isPChar 'q' = Just (Element (Min2nd, 6) Cq)
isPChar 'r' = Just (Element (Min2nd, 7) Cr)
isPChar 's' = Just (Element (Min2nd, 8) Cs)
isPChar 't' = Just (Element (Min2nd, 9) Ct)
isPChar 'u' = Just (Element (Min3rd, 0) Cu)
isPChar 'v' = Just (Element (Min3rd, 1) Cv)
isPChar 'w' = Just (Element (Min3rd, 2) Cw)
isPChar 'x' = Just (Element (Min3rd, 3) Cx)
isPChar 'y' = Just (Element (Min3rd, 4) Cy)
isPChar 'z' = Just (Element (Min3rd, 5) Cz)
isPChar 'A' = Just (Element (Maj1st, 0) CA)
isPChar 'B' = Just (Element (Maj1st, 1) CB)
isPChar 'C' = Just (Element (Maj1st, 2) CC)
isPChar 'D' = Just (Element (Maj1st, 3) CD)
isPChar 'E' = Just (Element (Maj1st, 4) CE)
isPChar 'F' = Just (Element (Maj1st, 5) CF)
isPChar 'G' = Just (Element (Maj1st, 6) CG)
isPChar 'H' = Just (Element (Maj1st, 7) CH)
isPChar 'I' = Just (Element (Maj1st, 8) CI)
isPChar 'J' = Just (Element (Maj1st, 9) CJ)
isPChar 'K' = Just (Element (Maj2nd, 0) CK)
isPChar 'L' = Just (Element (Maj2nd, 1) CL)
isPChar 'M' = Just (Element (Maj2nd, 2) CM)
isPChar 'N' = Just (Element (Maj2nd, 3) CN)
isPChar 'O' = Just (Element (Maj2nd, 4) CO)
isPChar 'P' = Just (Element (Maj2nd, 5) CP)
isPChar 'Q' = Just (Element (Maj2nd, 6) CQ)
isPChar 'R' = Just (Element (Maj2nd, 7) CR)
isPChar 'S' = Just (Element (Maj2nd, 8) CS)
isPChar 'T' = Just (Element (Maj2nd, 9) CT)
isPChar 'U' = Just (Element (Maj3rd, 0) CU)
isPChar 'V' = Just (Element (Maj3rd, 1) CV)
isPChar 'W' = Just (Element (Maj3rd, 2) CW)
isPChar 'X' = Just (Element (Maj3rd, 3) CX)
isPChar 'Y' = Just (Element (Maj3rd, 4) CY)
isPChar 'Z' = Just (Element (Maj3rd, 5) CZ)
isPChar  _  = Nothing

--------------------------------------------------------------------------------------------------- 
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_PChar_injective : (x : PChar v i) -> (y : PChar v j) -> i = j
lemma_PChar_injective C_ C_ = Refl
lemma_PChar_injective C' C' = Refl
lemma_PChar_injective C0 C0 = Refl
lemma_PChar_injective C1 C1 = Refl
lemma_PChar_injective C2 C2 = Refl
lemma_PChar_injective C3 C3 = Refl
lemma_PChar_injective C4 C4 = Refl
lemma_PChar_injective C5 C5 = Refl
lemma_PChar_injective C6 C6 = Refl
lemma_PChar_injective C7 C7 = Refl
lemma_PChar_injective C8 C8 = Refl
lemma_PChar_injective C9 C9 = Refl
lemma_PChar_injective Ca Ca = Refl
lemma_PChar_injective Cb Cb = Refl
lemma_PChar_injective Cc Cc = Refl
lemma_PChar_injective Cd Cd = Refl
lemma_PChar_injective Ce Ce = Refl
lemma_PChar_injective Cf Cf = Refl
lemma_PChar_injective Cg Cg = Refl
lemma_PChar_injective Ch Ch = Refl
lemma_PChar_injective Ci Ci = Refl
lemma_PChar_injective Cj Cj = Refl
lemma_PChar_injective Ck Ck = Refl
lemma_PChar_injective Cl Cl = Refl
lemma_PChar_injective Cm Cm = Refl
lemma_PChar_injective Cn Cn = Refl
lemma_PChar_injective Co Co = Refl
lemma_PChar_injective Cp Cp = Refl
lemma_PChar_injective Cq Cq = Refl
lemma_PChar_injective Cr Cr = Refl
lemma_PChar_injective Cs Cs = Refl
lemma_PChar_injective Ct Ct = Refl
lemma_PChar_injective Cu Cu = Refl
lemma_PChar_injective Cv Cv = Refl
lemma_PChar_injective Cw Cw = Refl
lemma_PChar_injective Cx Cx = Refl
lemma_PChar_injective Cy Cy = Refl
lemma_PChar_injective Cz Cz = Refl
lemma_PChar_injective CA CA = Refl
lemma_PChar_injective CB CB = Refl
lemma_PChar_injective CC CC = Refl
lemma_PChar_injective CD CD = Refl
lemma_PChar_injective CE CE = Refl
lemma_PChar_injective CF CF = Refl
lemma_PChar_injective CG CG = Refl
lemma_PChar_injective CH CH = Refl
lemma_PChar_injective CI CI = Refl
lemma_PChar_injective CJ CJ = Refl
lemma_PChar_injective CK CK = Refl
lemma_PChar_injective CL CL = Refl
lemma_PChar_injective CM CM = Refl
lemma_PChar_injective CN CN = Refl
lemma_PChar_injective CO CO = Refl
lemma_PChar_injective CP CP = Refl
lemma_PChar_injective CQ CQ = Refl
lemma_PChar_injective CR CR = Refl
lemma_PChar_injective CS CS = Refl
lemma_PChar_injective CT CT = Refl
lemma_PChar_injective CU CU = Refl
lemma_PChar_injective CV CV = Refl
lemma_PChar_injective CW CW = Refl
lemma_PChar_injective CX CX = Refl
lemma_PChar_injective CY CY = Refl
lemma_PChar_injective CZ CZ = Refl

lemma_PChar_singleton : (x : PChar v i) -> (y : PChar v i) -> x = y
lemma_PChar_singleton C_ C_ = Refl
lemma_PChar_singleton C' C' = Refl
lemma_PChar_singleton C0 C0 = Refl
lemma_PChar_singleton C1 C1 = Refl
lemma_PChar_singleton C2 C2 = Refl
lemma_PChar_singleton C3 C3 = Refl
lemma_PChar_singleton C4 C4 = Refl
lemma_PChar_singleton C5 C5 = Refl
lemma_PChar_singleton C6 C6 = Refl
lemma_PChar_singleton C7 C7 = Refl
lemma_PChar_singleton C8 C8 = Refl
lemma_PChar_singleton C9 C9 = Refl
lemma_PChar_singleton Ca Ca = Refl
lemma_PChar_singleton Cb Cb = Refl
lemma_PChar_singleton Cc Cc = Refl
lemma_PChar_singleton Cd Cd = Refl
lemma_PChar_singleton Ce Ce = Refl
lemma_PChar_singleton Cf Cf = Refl
lemma_PChar_singleton Cg Cg = Refl
lemma_PChar_singleton Ch Ch = Refl
lemma_PChar_singleton Ci Ci = Refl
lemma_PChar_singleton Cj Cj = Refl
lemma_PChar_singleton Ck Ck = Refl
lemma_PChar_singleton Cl Cl = Refl
lemma_PChar_singleton Cm Cm = Refl
lemma_PChar_singleton Cn Cn = Refl
lemma_PChar_singleton Co Co = Refl
lemma_PChar_singleton Cp Cp = Refl
lemma_PChar_singleton Cq Cq = Refl
lemma_PChar_singleton Cr Cr = Refl
lemma_PChar_singleton Cs Cs = Refl
lemma_PChar_singleton Ct Ct = Refl
lemma_PChar_singleton Cu Cu = Refl
lemma_PChar_singleton Cv Cv = Refl
lemma_PChar_singleton Cw Cw = Refl
lemma_PChar_singleton Cx Cx = Refl
lemma_PChar_singleton Cy Cy = Refl
lemma_PChar_singleton Cz Cz = Refl
lemma_PChar_singleton CA CA = Refl
lemma_PChar_singleton CB CB = Refl
lemma_PChar_singleton CC CC = Refl
lemma_PChar_singleton CD CD = Refl
lemma_PChar_singleton CE CE = Refl
lemma_PChar_singleton CF CF = Refl
lemma_PChar_singleton CG CG = Refl
lemma_PChar_singleton CH CH = Refl
lemma_PChar_singleton CI CI = Refl
lemma_PChar_singleton CJ CJ = Refl
lemma_PChar_singleton CK CK = Refl
lemma_PChar_singleton CL CL = Refl
lemma_PChar_singleton CM CM = Refl
lemma_PChar_singleton CN CN = Refl
lemma_PChar_singleton CO CO = Refl
lemma_PChar_singleton CP CP = Refl
lemma_PChar_singleton CQ CQ = Refl
lemma_PChar_singleton CR CR = Refl
lemma_PChar_singleton CS CS = Refl
lemma_PChar_singleton CT CT = Refl
lemma_PChar_singleton CU CU = Refl
lemma_PChar_singleton CV CV = Refl
lemma_PChar_singleton CW CW = Refl
lemma_PChar_singleton CX CX = Refl
lemma_PChar_singleton CY CY = Refl
lemma_PChar_singleton CZ CZ = Refl

--------------------------------------------------------------------------------------------------- 
-- [Total Orders] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| x < y
data LTPChar : (x : PChar v i) -> (y : PChar w j) -> Type where
  IsLTNat : {x  : PChar v (k,i)}
         -> {y  : PChar w (k,j)}
         -> (lt : LTNat i j)
         -> LTPChar x y
  IsLTCharKind : {x  : PChar v (kv,i)}
              -> {y  : PChar w (kw,j)}
              -> (lt : LTCharKind kv kw)
              -> LTPChar x y

isLTPChar_gt : {x   : PChar v (ki, ni)}
            -> {y   : PChar w (kj, nj)}
            -> (gte : Not (LTCharKind ki kj))
            -> (neq : Not (ki = kj))
            -> LTPChar x y
            -> Void
isLTPChar_gt gte neq (IsLTNat lt) = neq Refl
isLTPChar_gt gte neq (IsLTCharKind lt) = gte lt

isLTPChar_neither : {x     : PChar v (ki, ni)}
                 -> {y     : PChar w (kj, nj)}
                 -> (gte_k : Not (LTCharKind ki kj))
                 -> (gte_n : Not (LTNat ni nj))
                 -> LTPChar x y
                 -> Void
isLTPChar_neither gte_k gte_n (IsLTNat lt) = gte_n lt
isLTPChar_neither gte_k gte_n (IsLTCharKind lt) = gte_k lt

isLTPChar : (x : PChar v i) -> (y : PChar w j) -> Dec (LTPChar x y)
isLTPChar {i = (ki,ni)} {j = (kj,nj)} x y with (isLTCharKind ki kj)
  | Yes lt = Yes (IsLTCharKind lt)
  | No gte_k =
    case decEq ki kj of
      No  neq  => No (isLTPChar_gt gte_k neq)
      Yes Refl =>
        case isLTNat ni nj of
          Yes lt    => Yes (IsLTNat lt)
          No  gte_n => No (isLTPChar_neither gte_k gte_n)

singLTPChar : (x   : PChar v i)
           -> (y   : PChar w j)
           -> (p,q : LTPChar x y)
           -> p = q
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTNat q) =
  case singLTNat i j p q of Refl => Refl
singLTPChar {i = (kv,i)} {j = (kw,j)} x y (IsLTCharKind p) (IsLTCharKind q) =
  case singLTCharKind kv kw p q of Refl => Refl
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymNum) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMin2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMin3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMin3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj1st) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj1stMaj2nd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj1stMaj3rd) impossible
singLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj2ndMaj3rd) impossible

irreflLTPChar : (x : PChar v i) -> (p : LTPChar x x) -> Void
irreflLTPChar {i = (k,i)} x (IsLTNat lt) = irreflLTNat i lt
irreflLTPChar {i = (k,i)} x (IsLTCharKind lt) = irreflLTCharKind k lt

antisymLTPChar : (x : PChar v i)
              -> (y : PChar w j)
              -> (p : LTPChar x y)
              -> (q : LTPChar y x)
              -> Void
antisymLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTNat q) = antisymLTNat i j p q
antisymLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind q) = irreflLTCharKind k q
antisymLTPChar {i = (k,i)} {j = (k,j)} x y (IsLTCharKind p) (IsLTNat q) = irreflLTCharKind k p
antisymLTPChar {i = (kv,i)} {j = (kw,j)} x y (IsLTCharKind p) (IsLTCharKind q) =
  antisymLTCharKind kv kw p q

decEq_char : {x : PChar v i} -> {y : PChar w j} -> (neq : Not (v = w)) -> (x = y) -> Void
decEq_char neq Refl = neq Refl

decEq : (x : PChar v i) -> (y : PChar w j) -> Dec (x = y)
decEq {v} {w} {i = (kv,i)} {j = (kw,j)} x y with (decEq v w)
  decEq {v = v} {w} {i = (kv,i)} {j = (kw,j)} x y | No  neq  = No (decEq_char neq)
  decEq {v = w} {w} {i = (kv,i)} {j = (kw,j)} x y | Yes Refl =
    case lemma_PChar_injective x y of
      Refl => Yes (lemma_PChar_singleton x y)
