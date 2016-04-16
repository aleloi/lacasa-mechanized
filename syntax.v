Require Import partial.
Require Import namesAndTypes.

Import ConcreteEverything.

Inductive Expr := 
| Null : Expr
| Var : VarName_type -> Expr
| FieldSelection : VarName_type -> FieldName_type -> Expr
| FieldAssignment : VarName_type -> FieldName_type -> VarName_type -> Expr
| MethodInvocation : VarName_type -> MethodName_type -> VarName_type -> Expr
| New : class -> Expr
| Box : class -> Expr
| Open : VarName_type -> VarName_type -> Term -> Expr
with 

Term :=
| TVar : VarName_type -> Term
| TLet : VarName_type -> Expr -> Term -> Term.


Notation "'t_let' x <- e 't_in' t" := (TLet x e t) (at level 0).


Definition flds := list (FieldName_type * class).
Definition varDefs := list (VarName_type * class).

Record MethDecl : Type := mkMethodDecl {
                              name: MethodName_type;
                              argType: typecheck_type;
                              argName: VarName_type;
                              retType: typecheck_type;
                              methodBody: Term;
                            }.

Record ClassDecl : Type := mkClassDecl {
                               cls: class;
                               cdFields: flds;
                               methods: list MethDecl 
                             }.

Record Program : Type := mkProgram {
                             classDecls : list ClassDecl;
                             globals : varDefs;
                             programBody: Term;
                           }.


