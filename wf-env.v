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

  Definition subtypeP := subtype P.

  Definition

  