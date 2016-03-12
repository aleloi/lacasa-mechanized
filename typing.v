Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import Coq.Structures.Equalities.

Module Typing (VarNameM FieldNameM MethodNameM ClassNameM RefM: Typ)
       (act: AbstractClassTable)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)
       (v5: Nice RefM).
  
  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                        v1 v2 v3 v4.
  (* Module hip := Heap FieldNameM ClassNameM RefM *)
  (*                    v2 v5. *)

  Module sfr := SFrame VarNameM FieldNameM MethodNameM ClassNameM RefM
                       v1 v2 v3 v4 v5.
  Import sfr.

  Module ct := ClassTable VarNameM FieldNameM MethodNameM ClassNameM
                          act v1 v2 v3 v4.
  (* Import ct. *)

  Import syn.
  (* Import hip. *)

  Inductive typecheck_type :=
  | class : ClassName -> typecheck_type
  | box : ClassName -> typecheck_type
  | all : typecheck_type.

  Inductive effect :=
  | eff_ocap : effect
  | epsilon : effect.
  
  Module tyM <: Typ.
    Definition t := typecheck_type.
  End tyM.

  Module part_gamma := Update VarNameM tyM v1.

  Notation gamma_ty := part_gamma.PartFunc.

  Inductive subtype : typecheck_type -> typecheck_type -> Prop :=
  | classSub : forall C D, ct.subclass C D -> subtype (class C) (class D)
  | boxSub : forall C D, ct.subclass C D -> subtype (box C) (box D)
  | allSub : forall sigma, subtype sigma all.

  Inductive TypeChecks : gamma_ty -> effect ->
                         ExprOrTerm -> typecheck_type -> Prop :=
  | T_Null : forall gamma eff,
               TypeChecks gamma eff Null all
                          
  | T_Var : forall gamma eff x sigma,
              part_gamma.func gamma x = Some sigma ->
              TypeChecks gamma eff (Var x) sigma

  | T_Field : forall gamma eff x f C,
              forall witn: ct.fld C f,
                part_gamma.func gamma x = Some (class C) ->
                TypeChecks gamma eff (FieldSelection x f)
                           (class (ct.ftype C f witn))

  | T_Assign : forall gamma eff x f y C D,
               forall witn: ct.fld C f,
                 part_gamma.func gamma y = Some (class C) ->
                 TypeChecks gamma eff (FieldSelection x f) (class D) ->
                 subtype (class C) (class D) ->
                 TypeChecks gamma eff (FieldAssignment x f y) (class C)

  (* TODO: Ocap! *)
  | T_New : forall gamma C eff,
              TypeChecks gamma eff (New C) (class C)

  | T_Open : forall gamma eff x C y t sigma,
                      TypeChecks gamma eff (Var x) (box C) ->
                      TypeChecks (part_gamma.updatePartFunc 
                                    part_gamma.emptyPartFunc
                                    y (class C)
                                 ) eff t sigma ->
                      TypeChecks gamma eff (Open x y t) (box C)

  | T_Let : forall gamma eff e sigma x tau t,
              TypeChecks gamma eff e sigma ->
              TypeChecks (part_gamma.updatePartFunc gamma x sigma) eff
                         t tau ->
              TypeChecks gamma eff (TLet x e t) tau.


  

End Typing.

  
  
  