Require Import partial.
Require Import namesAndTypes.

Import ConcreteEverything.


Inductive ExprOrTerm :=
| Null : ExprOrTerm
| Var : VarName_type -> ExprOrTerm
| FieldSelection : VarName_type -> FieldName_type -> ExprOrTerm
| FieldAssignment : VarName_type -> FieldName_type -> VarName_type -> ExprOrTerm
| MethodInvocation : VarName_type -> MethodName_type -> VarName_type -> ExprOrTerm
| New : ClassName_type -> ExprOrTerm
| Box : ClassName_type -> ExprOrTerm

(* x .open  y      =>    t *)
| Open : VarName_type -> VarName_type -> ExprOrTerm -> ExprOrTerm
| TLet : VarName_type -> ExprOrTerm -> ExprOrTerm -> ExprOrTerm.

Notation "'t_let' x <- e 't_in' t" := (TLet x e t) (at level 0).

Fixpoint isTerm (e: ExprOrTerm) : Prop :=
  match e with
    | Var _ => True
    | TLet _ e t => (fix isExpr (e: ExprOrTerm) : Prop :=
                       match e with
                         | TLet _ _ _ => False
                         | Open _ _ t' => isTerm t'
                         | _ => True
                       end
                    ) e /\ isTerm t
    | _ => False
  end.

Definition isExpr (e: ExprOrTerm) : Prop :=
  match e with
    | TLet _ _ _ => False
    | Open _ _ t => isTerm t
    | _ => True
  end.


Inductive class :=
| AnyRef : class
| extends : ClassName_type -> class -> class.

Definition flds := list (FieldName_type * ClassName_type).
Definition varDefs := list (VarName_type * ClassName_type).

Inductive ty :=
| simple : ClassName_type -> ty
| box : ClassName_type -> ty.

Record MethDecl : Type := mkMethodDecl {
                              name: MethodName_type;
                              argType: ty;
                              argName: VarName_type;
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


