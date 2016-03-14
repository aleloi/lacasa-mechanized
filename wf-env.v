Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import typing.
Require Import namesAndTypes.

Import ConcreteEverything.

Section Preservation.

  Definition gamma_env_subset (gamma: Gamma_type) (L: Env_type) :=
    forall x sigma envOb,
      p_gamma.func gamma x = Some sigma ->
      p_env.func L x = Some envOb.

  Import Coq.Lists.List.

  Definition heap_typeof (H: Heap_type) (o: Ref_type)
             (witn: In o (p_heap.domain H)) :
    ClassName_type.
    set (lem := proj2 (p_heap.fDomainCompat H o)).
    case_eq (p_heap.func H o).
    intros;    destruct b;    exact c.
    intro is_none; set (is_absurd := lem is_none); auto.
  Defined.

  Parameter P: Program.

  Print heap_typeof.

  Definition subtypeP := subtype P.

  Local Open Scope type_scope.

  Print sum.

  Definition WF_Var (H: Heap_type) (Gamma: Gamma_type) (L: Env_type) (x: VarName_type):=
    (p_env.func L x = Some envNull) +
    {C_o |
     match C_o with
       | (C, o) => {witn |
                    p_gamma.func Gamma x = Some (typt_class C) /\
                    subtypeP (typt_class (heap_typeof H o witn)) (typt_class C)
                   }
     end} +
    {C_o |
     match C_o with
       | (C, o) => {witn |
                    p_gamma.func Gamma x = Some (typt_box C) /\
                    subtypeP (typt_class (heap_typeof H o witn)) (typt_class C)
                   }
     end}.

  Definition WF_Env H Gamma L :=
    gamma_env_subset Gamma L *
    forall x sigma,
      p_gamma.func Gamma x = Some sigma ->
      WF_Var H Gamma L x.

  Inductive T_Frame1 : Heap_type -> ann_frame_type -> typecheck_type -> Type :=
  | t_frame : forall H Gamma eff t L ann sigma,
                isTerm t ->
                TypeChecks Gamma eff t sigma ->
                WF_Env H Gamma L ->
                T_Frame1 H (ann_frame (sframe L t) ann) sigma.
