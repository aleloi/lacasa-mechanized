Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import Coq.Structures.Equalities.


Module SFrame (VarNameM FieldNameM MethodNameM ClassNameM RefM: Typ)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)
       (v5: Nice RefM).

  Definition refType := RefM.t.

  
  Inductive envRangeTy :=
  | envNull : envRangeTy
  | ref : refType -> envRangeTy
  | box : refType -> envRangeTy.

  Module ert <: Typ.
    Definition t := envRangeTy.
  End ert.

  

  Module part_env := Update VarNameM ert v1.
  Notation env_ty := part_env.PartFunc.

  Module syn := Syntax  VarNameM FieldNameM MethodNameM ClassNameM
                        v1 v2 v3 v4.
  Module hip := Heap FieldNameM ClassNameM RefM
                        v2 v5.
  (* Print syn. *)
  Inductive sframe_ty :=
  | sframe : env_ty -> syn.ExprOrTerm -> sframe_ty.
  (* Alternatives:
   *  1. Change language to allow exprs, not terms in sframe. Add reduction rules. Modify progress theorem conclusion.
   *
   *  2. Add isTerm here
   *  3. Add isTerm somewhere in well-formedness
   *  4. Don't do anything here, but do not add extra reduction rules. Modify progress theorem conclusion (slightly).
   * 
   *)

  Inductive sf_config :=
  | heap_sframe : hip.Heap_ty -> sframe_ty -> sf_config.

  Notation "( # H , L , t ! )" := (heap_sframe H (sframe L t)) (at level 0).
    
End SFrame.