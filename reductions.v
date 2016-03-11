Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import Coq.Structures.Equalities.

Module Reductions (VarNameM FieldNameM MethodNameM ClassNameM RefM: Typ)
       (act: AbstractClassTable)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)
       (v5: Nice RefM).

  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                        v1 v2 v3 v4.
  Module hip := Heap FieldNameM ClassNameM RefM
                     v2 v5.

  Module sfr := SFrame VarNameM FieldNameM MethodNameM ClassNameM RefM
                       v1 v2 v3 v4 v5.
  Import sfr.

  Module ct := ClassTable VarNameM FieldNameM MethodNameM ClassNameM
                          act v1 v2 v3 v4.

  Import syn.
  Import sfr.
  Import hip.
  Notation "( p +++ a --> b )" := (part_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o --> obj )" := (part_Heap.updatePartFunc
                                              H o obj)
                                      (at level 0).
  Notation heapUpd := part_Heap.updatePartFunc.

  (* Notation "$$ C FM $$" := (obj C FM) (at level 201). *)

  (* let x = y in t*)
  Import Coq.Lists.List.
  Inductive Reduction :
    sf_config -> sf_config -> Prop :=
  | E_Var : forall x y t H L null_ref_box,
              syn.isTerm t -> 
              part_env.func L y = Some null_ref_box ->
              Reduction ( # H , L , t_let x <- (Var y) t_in t ! )
                        ( # H , (L +++ x --> null_ref_box) , t !)

  | E_Null : forall x t H L,
              syn.isTerm t -> 
              Reduction ( # H , L , t_let x <- Null t_in t ! )
                        ( # H , (L +++ x --> envNull) , t !)

  | E_New : forall C o x t H L FM obj,
              syn.isTerm t ->
              ~ In o (part_Heap.domain H) ->
              FM = hip.part_FM.newPartFunc (fields C) null ->
              (* obj = ( $$ C FM $$ ) -> *)
               Reduction ( # H , L , t_let x <- New C t_in t ! )
                         ( # H ,
                           ( L +++ x --> envNull ) , t ! ).