Require Import partial.
Require Import namesAndTypes.

        
Module Syntax (ant: AbstractNamesAndTypes).
       
  Definition VarType := ant.VarNameM.t.
  (* Everything is actually nat, but we abstract 
   * away VarType to reduce confusion.
   *)
  Definition FieldName := ant.FieldNameM.t.
  Definition MethodName := ant.MethodNameM.t.
  Definition ClassName := ant.ClassNameM.t.
  (* TODO: check what the article does! *)

  Inductive ExprOrTerm :=
  | Null : ExprOrTerm
  | Var : VarType -> ExprOrTerm
  | FieldSelection : VarType -> FieldName -> ExprOrTerm
  | FieldAssignment : VarType -> FieldName -> VarType -> ExprOrTerm
  | MethodInvocation : VarType -> MethodName -> VarType -> ExprOrTerm
  | New : ClassName -> ExprOrTerm
  | Box : ClassName -> ExprOrTerm

           (* x .open  y      =>    t *)
  | Open : VarType -> VarType -> ExprOrTerm -> ExprOrTerm
  | TLet : VarType -> ExprOrTerm -> ExprOrTerm -> ExprOrTerm.

  Notation "'t_let' x <- e 't_in' t" := (TLet x e t) (at level 0).

  Definition isExpr (e: ExprOrTerm) : Prop :=
    match e with
      | TLet _ _ _ => False
      | _ => True      
    end.

  Fixpoint isTerm (e: ExprOrTerm) : Prop :=
    match e with
      | Var _ => True
      | TLet _ e t => isExpr e /\ isTerm t
      | _ => False
    end.

  Inductive class :=
  | AnyRef : class
  | extends : ClassName -> class -> class.

  Definition flds := list (FieldName * ClassName).
  Definition varDefs := list (VarType * ClassName).
  
  Inductive ty :=
  | simple : ClassName -> ty
  | box : ClassName -> ty.

  Record MethDecl : Type := mkMethodDecl {
                           name: MethodName;
                           argType: ty;
                           argName: VarType;
                           retType: ty;
                           methodBody: ExprOrTerm;
                           methodBodyIsTerm : isTerm methodBody
                              }.
                               
  Record ClassDecl : Type := mkClassDecl {
                                 cls: class;
                                 fields: flds;
                                 methods: list MethDecl 
                               }.

  Record Program : Type := mkProgram {
                               classDecls : list ClassDecl;
                               globals : list varDefs;
                               programBody: ExprOrTerm;
                               programBodyIsTerm : isTerm programBody
                             }.
  
End Syntax.

