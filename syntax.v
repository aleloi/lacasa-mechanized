Require Import partial.
Require Import namesAndTypes.

Import ConcreteEverything.


Inductive ExprOrTerm :=
| Null : ExprOrTerm
| Var : VarName_type -> ExprOrTerm
| FieldSelection : VarName_type -> FieldName_type -> ExprOrTerm
| FieldAssignment : VarName_type -> FieldName_type -> VarName_type -> ExprOrTerm
| MethodInvocation : VarName_type -> MethodName_type -> VarName_type -> ExprOrTerm
| New : class -> ExprOrTerm
| Box : class -> ExprOrTerm

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




Definition flds := list (FieldName_type * class).
Definition varDefs := list (VarName_type * class).

Record MethDecl : Type := mkMethodDecl {
                              name: MethodName_type;
                              argType: typecheck_type;
                              argName: VarName_type;
                              retType: typecheck_type;
                              methodBody: ExprOrTerm;
                              methodBodyIsTerm : isTerm methodBody
                            }.

Record ClassDecl : Type := mkClassDecl {
                               cls: class;
                               cdFields: flds;
                               methods: list MethDecl 
                             }.

Record Program : Type := mkProgram {
                             classDecls : list ClassDecl;
                             globals : varDefs;
                             programBody: ExprOrTerm;
                             programBodyIsTerm : isTerm programBody
                           }.


