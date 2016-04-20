Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import namesAndTypes.
Require Import ocap.


Import ConcreteEverything.

Section Typing.
  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.

  Inductive TypeChecksExpr : Gamma_type -> effect ->
                         Expr -> typecheck_type -> Type :=
  | T_Null : forall gamma eff,
               TypeChecksExpr gamma eff Null typt_all
                          
  | T_Var : forall gamma eff x sigma,
              p_Γ.func gamma x = Some sigma ->
              TypeChecksExpr gamma eff (Var x) sigma

  | T_Field : forall gamma eff x f C,
              forall witn: fldP C f,
                p_Γ.func gamma x = Some (typt_class C) ->
                TypeChecksExpr gamma eff (FieldSelection x f)
                           (typt_class (ftypeP C f witn))

  | T_Assign : forall gamma eff x f y C D,
               forall witn: fldP C f,
                 p_Γ.func gamma y = Some (typt_class C) ->
                 TypeChecksExpr gamma eff (FieldSelection x f) (typt_class D) ->
                 subtypeP (typt_class C) (typt_class D) ->
                 TypeChecksExpr gamma eff (FieldAssignment x f y) (typt_class C)

  (* TODO: Ocap! *)
  | T_New_ocap :
      forall gamma C,
        ocap P C ->
        TypeChecksExpr gamma eff_ocap (New C) (typt_class C)

  | T_New_not_ocap :
      forall gamma C,
        TypeChecksExpr gamma eff_epsilon (New C) (typt_class C)

  | T_Box :
      forall gamma C,
        ocap P C ->
        TypeChecksExpr gamma eff_ocap (Box C) (typt_box C)


  | T_Invoke :
      forall gamma C y m z md eff sigma , (* TODO recursion and well-formedness*)
      forall (witn: method P C m md),
        p_Γ.func gamma y = Some (typt_class C) ->
        p_Γ.func gamma z = Some sigma ->
        subtypeP sigma (argType md) ->
        TypeChecksExpr gamma eff (MethodInvocation y m z) (retType md)
  

  | T_Open : forall gamma eff x C y t sigma,
               TypeChecksExpr gamma eff (Var x) (typt_box C) ->
               TypeChecksTerm (p_Γ.updatePartFunc 
                             p_Γ.emptyPartFunc
                             y (typt_class C)
                          ) eff_ocap t sigma ->
               TypeChecksExpr gamma eff (Open x y t) (typt_box C)

  with
  TypeChecksTerm : Gamma_type -> effect ->
                   Term -> typecheck_type -> Type :=

  | T_Let : forall gamma eff e sigma x tau t,
              TypeChecksExpr gamma eff e sigma ->
              TypeChecksTerm (p_Γ.updatePartFunc gamma x sigma) eff
                         t tau ->
              TypeChecksTerm gamma eff (TLet x e t) tau

  | T_Var_T : forall gamma eff x sigma,
              p_Γ.func gamma x = Some sigma ->
              TypeChecksTerm gamma eff (TVar x) sigma.

End Typing.

  
  
  