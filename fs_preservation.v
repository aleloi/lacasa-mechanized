Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import typing.
Require Import namesAndTypes.

Require Import preservation.

Require Import wf_env.

Import ConcreteEverything.

Section Preservation.

  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  Definition t_frame1' := t_frame1 P.
  Definition WF_Frame' := WF_Frame P.

  Definition Reduction_SF' := Reduction_SF P.
  Definition Reduction_FS' := Reduction_FS P.
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecks P.
  Definition Heap_okP := Heap_ok P.

  Notation "[ H , x , tau ## FS ]" := (WF_FS P (Some (x, tau)) H FS) (at level 0).
  Notation "[ H ## FS ]" := (WF_FS P None H FS) (at level 0).

  Theorem multiple_frame_WF_ENV_preservation :
    forall H H' FS FS',
      Reduction_FS' (H, FS)
                   (H', FS') ->
      Heap_okP H ->
      [ H ## FS ]  ->
      [ H' ## FS' ] * (Heap_okP H').

    intros.
    inversion X.
    (* 4 goals,  based on reduction rule:
     * E-frame-stack,
     * E-return1
     * E-return2
     * E-open
     *)

    (* CASE E-frame-stack, 
     * H, F -> H', F',
     * H, F :: FS --> H', F' :: FS
     *)

    admit.
    (* TODO put in own theorem *)


    (* Case E-return *)
    admit. 
    
    (* Case E-open-return *)
    rewrite <- H4 in *.
    rewrite <- H6 in *.
    rewrite <- H5 in *.
    clear H5 H6 H3 H1.
    split.
    
    inversion X0;
    assumption.
    assumption.


    (* Case E-open *)
    admit.
  Admitted.

End Preservation.