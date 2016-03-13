Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import namesAndTypes.

Import ConcreteEverything.

Section Typing.
  Parameter P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.

  Inductive TypeChecks : Gamma_type -> effect ->
                         ExprOrTerm -> typecheck_type -> Type :=
  | T_Null : forall gamma eff,
               TypeChecks gamma eff Null typt_all
                          
  | T_Var : forall gamma eff x sigma,
              p_gamma.func gamma x = Some sigma ->
              TypeChecks gamma eff (Var x) sigma

  | T_Field : forall gamma eff x f C,
              forall witn: fldP C f,
                p_gamma.func gamma x = Some (typt_class C) ->
                TypeChecks gamma eff (FieldSelection x f)
                           (typt_class (ftypeP C f witn))

  | T_Assign : forall gamma eff x f y C D,
               forall witn: fldP C f,
                 p_gamma.func gamma y = Some (typt_class C) ->
                 TypeChecks gamma eff (FieldSelection x f) (typt_class D) ->
                 subtypeP (typt_class C) (typt_class D) ->
                 TypeChecks gamma eff (FieldAssignment x f y) (typt_class C)

  (* TODO: Ocap! *)
  | T_New : forall gamma C eff,
              TypeChecks gamma eff (New C) (typt_class C)

  | T_Open : forall gamma eff x C y t sigma,
                      TypeChecks gamma eff (Var x) (typt_box C) ->
                      TypeChecks (p_gamma.updatePartFunc 
                                    p_gamma.emptyPartFunc
                                    y (typt_class C)
                                 ) eff t sigma ->
                      TypeChecks gamma eff (Open x y t) (typt_box C)

  | T_Let : forall gamma eff e sigma x tau t,
              TypeChecks gamma eff e sigma ->
              TypeChecks (p_gamma.updatePartFunc gamma x sigma) eff
                         t tau ->
              TypeChecks gamma eff (TLet x e t) tau.

  

End Typing.

  
  
  