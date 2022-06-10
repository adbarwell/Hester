module Transform.Rename.SSimplification

import public Hs98Simplified
import public Hs98

%default total

export
fromDP : {P : a -> Type} -> (x : a ** P x) -> Subset a P
fromDP (x ** prf) = Element x prf

-- [Literals] -------------------------------------------------------------------------------------

public export
data StructLiteral : (l1 : HsLiteralTy) -> (l2 : SHsLiteralTy) -> Type where 
  MkStructLit : StructLiteral (HsInt l) (SHsInt l)

export
transStructLit : (l1 : HsLiteralTy) -> (l2 : SHsLiteralTy ** StructLiteral l1 l2) 
transStructLit (HsInt i) = (SHsInt i ** MkStructLit)

-- [Names] ----------------------------------------------------------------------------------------

public export
data StructName : (n1 : HsNameTy kind) -> (n2 : SHsNameTy) -> Type where
  MkStructNameVar : StructName (HsIdentVar lv id na) (SHsIdentVar lv id)
  MkStructNameCtr : StructName (HsIdentCtr id na) (SHsIdentCtr id)

export
transStructName : (n1 : HsNameTy kind) -> (n2 : SHsNameTy ** StructName n1 n2)
transStructName (HsIdentVar lv id na) = (SHsIdentVar lv id ** MkStructNameVar)
transStructName (HsIdentCtr id na) = (SHsIdentCtr id ** MkStructNameCtr)

-- [Patterns] -------------------------------------------------------------------------------------

public export
data StructPatDef : (p1 : HsPatDefTy bound env) -> (p2 : SHsPatDefTy) -> Type where
  MkStructPatDefVar : StructName na1 na2 -> StructPatDef (HsPVar na1) (SHsPVar na2)
  MkStructPatDefApp : StructPatDef (HsPApp ctr1 args1) (SHsPApp args1)

export
transStructPatDef : (p1 : HsPatDefTy bound env) -> (p2 : SHsPatDefTy ** StructPatDef p1 p2)
transStructPatDef (HsPVar na) =
  case transStructName na of 
    (n1 ** naPrf) => (SHsPVar n1 ** MkStructPatDefVar naPrf)
transStructPatDef (HsPApp ctrs args) =
  (SHsPApp args ** MkStructPatDefApp)

public export
data StructPat : (p1 : HsPatTy env) -> (p2 : SHsPatTy) -> Type where
  MkStructPat : Map StructPatDef defs1 defs2 
             -> StructPat (HsPat defs1) (SHsPat defs2)

export
transStructPat : (p1 : HsPatTy env) 
              -> (p2 : SHsPatTy ** StructPat p1 p2)
transStructPat (HsPat defs) =
  case map (\p => fromDP (transStructPatDef p)) defs of
    Element x prf => 
       (SHsPat x ** MkStructPat prf)

-- [Expressions] ----------------------------------------------------------------------------------

public export
data StructExp : (e1 : HsExpTy env) -> (e2 : SHsExpTy) -> Type where
  MkStructExpVar : StructName na1 na2 -> StructExp (HsVar na1) (SHsVar na2)

  MkStructExpLit : StructLiteral l1 l2 -> StructExp (HsLit l1) (SHsLit l2)

  MkStructExpApp : StructExp e1 e2 -> StructExp e3 e4 -> StructExp (HsApp e1 e3) (SHsApp e2 e4)

  MkStructExpLam : Map StructPat ps1 ps2 
                -> StructExp e1 e2 
                -> StructExp (HsLambda ps1 e1) (SHsLambda ps2 e2)

  MkStructExpPar : StructExp e1 e2 -> StructExp (HsParen e1) (SHsParen e2)

export
transStructExp : (e1 :  HsExpTy env) -> (e2 : SHsExpTy ** StructExp e1 e2 )
transStructExp (HsVar na1) =
  case transStructName na1 of 
    (na1' ** naPrf) => (SHsVar na1' ** MkStructExpVar naPrf)
transStructExp (HsLit li) = 
  case transStructLit li of 
    (li' ** liPrf) => (SHsLit li' ** MkStructExpLit liPrf)
transStructExp (HsApp e1 e2) =
  case transStructExp e1 of 
    (e1' ** e1Prf) =>
      case transStructExp e2 of 
        (e2' ** e2Prf) => (SHsApp e1' e2' ** MkStructExpApp e1Prf e2Prf) 
transStructExp (HsLambda ps e) =
  case map (\p => fromDP (transStructPat p)) ps of
    Element x prf => 
      case transStructExp e of 
        (e' ** ePrf) =>
            (SHsLambda x e' ** MkStructExpLam prf ePrf)
transStructExp (HsParen e) =
  case transStructExp e of 
    (e' ** prf) => (SHsParen e' ** MkStructExpPar prf)

-- [Declarations] ---------------------------------------------------------------------------------

public export
data StructDeclKind : (k : HsDeclKindTy) -> (ks : SHsDeclKindTy) -> Type where
  MkStructDeclKindDecl : StructDeclKind (Decl _ _) SDecl
  MkStructDeclKindFunClause : StructDeclKind (FunClause _) SFunClause

export
transStructKind : (k : HsDeclKindTy) -> (k' : SHsDeclKindTy ** StructDeclKind k k')
transStructKind (Decl _ _) = (SDecl ** MkStructDeclKindDecl)
transStructKind (FunClause _) = (SFunClause ** MkStructDeclKindFunClause)

public export
data StructDecl : (d1 : HsDeclTy env kind) -> (d1s : SHsDeclTy kind2) -> Type where

  MkStructDeclMatch : Map StructPat ps ps2 
                   -> StructExp e e2 
                   -> Map StructDecl ws ws2 
                   -> StructDecl (HsMatch ps e ws) (SHsMatch ps2 e2 ws2)

  MkStructDeclFun : StructName fname1 fname2 
                 -> Map StructDecl clauses1 clauses2 
                 -> StructDecl (HsFunBind fname1 clauses1) (SHsFunBind fname2 clauses2)

  MkStructDeclPat : StructPat p1 p2
                 -> StructExp e1 e2 
                 -> Map StructDecl ws1 ws2 
                 -> StructDecl (HsPatBind p1 e1 ws1) (SHsPatBind p2 e2 ws2)

export
transStructDecl : (d1 : HsDeclTy env kind) 
               -> (d1s : SHsDeclTy (fst (transStructKind kind)) ** (StructDecl d1 d1s))
transStructDecl (HsMatch ps e ws) = 
  case map (\p => fromDP (transStructPat p)) ps of
    Element ps' prf => 
      case transStructExp e of 
        (e' ** ePrf) =>
          case assert_total (map (\w => fromDP (transStructDecl w)) ws) of
            Element ws' wsPrf =>
              (SHsMatch ps' e' ws' ** MkStructDeclMatch prf ePrf wsPrf)

transStructDecl (HsFunBind fname1 clauses1) = 
  case transStructName fname1 of 
    (fname' ** prf) =>
      case assert_total (map (\w => fromDP (transStructDecl w)) clauses1) of
        Element ws' wsPrf =>
          (SHsFunBind fname' ws' ** MkStructDeclFun prf wsPrf)

transStructDecl (HsPatBind p e ws) = 
  case transStructPat p of
    (p' ** prf) => 
     case transStructExp e of 
        (e' ** ePrf) =>
          case assert_total (map (\w => fromDP (transStructDecl w)) ws) of
            Element ws' wsPrf =>
              (SHsPatBind p' e' ws' ** MkStructDeclPat prf ePrf wsPrf)

-- [Modules] ---------------------------------------------------------------------------------------

public export
data Struct : (m1 : HsModuleTy) -> (m1s : SHsModuleTy) -> Type where
  MkStruct : Map StructDecl decls decls2 -> Struct (HsModule env vars decls) (SHsModule decls2)

export
transStructModule : (m1 : HsModuleTy) -> (m1s : SHsModuleTy ** Struct m1 m1s)
transStructModule (HsModule env vars decls) =
  case assert_total (map (\w => fromDP (transStructDecl w)) decls) of
    Element ws' wsPrf =>
      (SHsModule ws' ** MkStruct wsPrf)

-- [Injectiveness]

export
injLit : (l : HsLiteralTy)
      -> (x,y : SHsLiteralTy)
      -> (p : StructLiteral l x)
      -> (q : StructLiteral l y)
      -> x = y
injLit (HsInt i) (SHsInt i) (SHsInt i) (MkStructLit) (MkStructLit) = Refl

export
injName : (n : HsNameTy kind)
       -> (x,y : SHsNameTy)
       -> (p : StructName n x)
       -> (q : StructName n y)
       -> x = y
injName (HsIdentVar lv1 id1 na0) (SHsIdentVar lv1 id1) (SHsIdentVar lv1 id1) (MkStructNameVar) (MkStructNameVar) = Refl
injName (HsIdentCtr id na) (SHsIdentCtr id) (SHsIdentCtr id) (MkStructNameCtr) (MkStructNameCtr) = Refl

export
injPatDef : (patDef : HsPatDefTy bound env)
         -> (x,y : SHsPatDefTy)
         -> (p : StructPatDef patDef x)
         -> (q : StructPatDef patDef y)
         -> x = y
injPatDef (HsPVar na0) (SHsPVar na1) (SHsPVar na2) (MkStructPatDefVar na3) (MkStructPatDefVar na4) = 
    case injName na0 na1 na2 na3 na4 of 
      Refl => Refl
injPatDef (HsPApp ctr0 args2) (SHsPApp args2) (SHsPApp args2) (MkStructPatDefApp) (MkStructPatDefApp) = Refl

export
injPat : (pat : HsPatTy env)
      -> (x,y : SHsPatTy)
      -> (p : StructPat pat x)
      -> (q : StructPat pat y)
      -> x = y
injPat (HsPat d0) (SHsPat d1) (SHsPat d2) (MkStructPat d3) (MkStructPat d4) = 
  case lemma_Map_injective injPatDef d3 d4 of 
    Refl => Refl 

export
injExp :  (e : HsExpTy env)
       -> (x,y : SHsExpTy)
       -> (p : StructExp e x)
       -> (q : StructExp e y)
       -> x = y
injExp (HsVar na0) (SHsVar na1) (SHsVar na2) (MkStructExpVar na3) (MkStructExpVar na4) =
  case injName na0 na1 na2 na3 na4 of
    Refl => Refl 
injExp (HsLit l0) (SHsLit l1) (SHsLit l2) (MkStructExpLit l11) (MkStructExpLit l22) = 
  case injLit l0 l1 l2 l11 l22 of 
    Refl => Refl 
injExp (HsApp e01 e02) (SHsApp e11 e12) (SHsApp e21 e22) (MkStructExpApp ee1 ee2) (MkStructExpApp ee3 ee4) = 
  case injExp e01 e11 e21 ee1 ee3 of 
    Refl => 
      case injExp e02 e12 e22 ee2 ee4 of 
        Refl => Refl
injExp (HsLambda ps0 e0) (SHsLambda ps1 e1) (SHsLambda ps2 e2) (MkStructExpLam ps3 e3) (MkStructExpLam ps4 e4) =
  case lemma_Map_injective injPat ps3 ps4 of 
    Refl => 
      case injExp e0 e1 e2 e3 e4 of
        Refl => Refl
injExp (HsParen e0) (SHsParen e1) (SHsParen e2) (MkStructExpPar e3) (MkStructExpPar e4) = 
  case injExp e0 e1 e2 e3 e4 of 
    Refl => Refl 

export
injDecl : (d : HsDeclTy env kind) 
       -> (x,y : SHsDeclTy kind2) 
       -> (p : StructDecl d x) 
       -> (q : StructDecl d y) 
       -> x = y   
injDecl (HsMatch ps00 e00 w00) (SHsMatch ps11 e11 ws11) (SHsMatch ps22 e22 ws22) (MkStructDeclMatch p1 e1 d1) (MkStructDeclMatch p2 e2 d2) =
  case lemma_Map_injective injPat p1 p2 of 
    Refl => 
      case injExp e00 e11 e22 e1 e2 of 
        Refl => 
          case lemma_Map_injective (assert_total injDecl)  d1 d2 of 
            Refl => Refl
injDecl (HsFunBind n0 ws0) (SHsFunBind n1 ws1) (SHsFunBind n2 ws2) (MkStructDeclFun nn1 cc1) (MkStructDeclFun nn2 cc2) = 
  case injName n0 n1 n2 nn1 nn2 of 
    Refl => 
      case lemma_Map_injective (assert_total injDecl) cc1 cc2 of 
        Refl => Refl  
injDecl (HsPatBind p0 e0 ws0) (SHsPatBind p1 e1 ws1) (SHsPatBind p2 e2 ws2) (MkStructDeclPat pp1 ee1 cc1) (MkStructDeclPat pp2 ee2 cc2) = 
  case injPat p0 p1 p2 pp1 pp2 of
    Refl =>
      case injExp e0 e1 e2 ee1 ee2 of 
        Refl => 
          case lemma_Map_injective (assert_total injDecl)  cc1 cc2 of 
            Refl => Refl 

export
inj : (m : HsModuleTy) 
   -> (x,y : SHsModuleTy) 
   -> (p : Struct m x) 
   -> (q : Struct m y) 
   -> x = y
inj (HsModule env vars decls) (SHsModule x) (SHsModule y) (MkStruct p') (MkStruct q') = 
  case lemma_Map_injective injDecl p' q' of
    Refl => Refl 

