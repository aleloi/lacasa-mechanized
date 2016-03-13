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

  Parameter P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.

  Print sigT.

  Print snd.
  Print pair.

  Theorem preservation_light :
    forall gamma H H' L L' t t' sigma eff,
      Reduction_SF ( # H, L, t !)
                   ( # H', L', t' !)
      ->
      TypeChecks gamma eff t sigma ->
      {sig_gam : prod typecheck_type Gamma_type  & TypeChecks (snd sig_gam) eff t' (fst sig_gam)}.
    intros.
    case_eq t; intros;  rewrite H0 in *  ;    clear H0 t; inversion X;
    inversion X0;
      exists (sigma , p_gamma.updatePartFunc gamma v sigma0); cbn;
      rewrite H9 in *; auto.
  Qed.

  