Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import typing.
Require Import namesAndTypes.
Require Import wf_env.

Import ConcreteEverything.

Section Preservation.

  Parameter P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  
  Theorem preservation_light :
    forall gamma H H' L L' t t' sigma eff,
      Reduction_SF ( # H, L, t !)
                   ( # H', L', t' !)
      ->
      TypeChecks gamma eff t sigma ->
      {Gamma' : Gamma_type & TypeChecks Gamma' eff t' sigma}.
    intros.
    case_eq t; intros;  rewrite H0 in *  ;    clear H0 t; inversion X;
    inversion X0;
      exists (p_gamma.updatePartFunc gamma v sigma0); cbn;
      rewrite H9 in *; auto.
  Qed.

  Theorem single_frame_WF_ENV_preservation :
    forall H H' L L' t t' sigma ann,
      WF_Frame H (ann_frame (sframe L t) ann) sigma ->
      Reduction_SF ( # H, L, t !) ( # H', L', t' !) ->
      WF_Frame H (ann_frame (sframe L' t') ann) sigma.
    intros.
    case_eq t; intros;   rewrite H0 in *  ;    clear H0 t;   inversion X0.

    rewrite <- H7 in *; clear H7 H1 H0.
    rewrite <- H8 in *; clear H2 L0 H8.
    rewrite <- H6 in *; rewrite <- H9 in *; clear  H9 H6.
    rewrite <- H5 in *; clear H5.
    rewrite <- H4 in *; clear H4.

    (* inversion H16. *)
    (* rewrite H2 in *; clear H2 H16 H5. *)
    (* rewrite <- H4 in *. *)
    (* clear H15 H4 v. *)
    (* clear L1 H11 t0 y0 x0. *)
    (* assert (Some null_ref_box0 = Some null_ref_box). transitivity (p_env.func L y). *)
    (* auto. auto. *)
    (* inversion H1. *)
    (* rewrite H4 in *. *)
    (* clear H4 H1 H8 H21 null_ref_box0. *)

    inversion X.
    clear H5 t0. clear H4 H1 H2 H6 L0 ann0 sigma0 H0. 
    
    inversion X1.
    clear gamma H0 x0 H4 eff0 H1 t0 H6 H2 tau H5 e.
    apply (t_frame1 H (p_gamma.updatePartFunc Gamma x sigma0) eff t
                    (p_env.updatePartFunc L x null_ref_box) ann sigma H3).
    apply X4.
    split.
    destruct X2.
    apply (subset_preserved _ _ _ _ _ g).
    intros.
    elim (v_eq_dec x x0).
    intro; rewrite <- a in *; clear a.

    inversion X3.
    clear H6 H4 H1; rewrite <- H2 in *; clear H2 sigma2.
    set (wf_var_y := snd X2 y sigma0 H5).
    
    (* 3.
     *)
    induction null_ref_box.
    (* 
     * 3. (a), L(y) = null
     *)
    apply inl; apply inl.
    apply (proj1 (p_env.updatedFuncProp L x envNull x) (eq_refl x)).

    (* 3. (b), L(y) = o*)
    rename r into o.
    rename H10 into _3_b_i_A. 
    induction  wf_var_y.
    induction a. (* case L(y) = null in WF-var *)
    rewrite a in _3_b_i_A; discriminate.

    induction b;  destruct x2. (* case L(y) = o', H(o') = <C, FM> in WF-var*)
    induction p.
    destruct p.
    rewrite (_3_b_i_A) in *; inversion H1.
    destruct H2.
    rewrite ->  H6 in *.
    clear o H6.
    rename r into o. (* it couldn't do it directly *)
    rename c into C'.
    clear H1.

    apply inl. apply inr.
    exists (C', o).
    exists x2.
    split.
    apply p_env.updatedFuncProp; apply eq_refl.
    split.

    set (lem := proj1 (p_gamma.updatedFuncProp gamma  x sigma0 x) (eq_refl x)).
    rewrite lem in H0; inversion H0; rewrite H6 in *.
    rename sigma1 into sigma'; clear H6 H0.
    rewrite H2 in H5; inversion H5; rewrite <- H1 in *.
    clear H1 sigma'.
    apply p_gamma.updatedFuncProp; apply eq_refl.
    auto.

    induction b; destruct x2; induction p; destruct p; destruct H2.

    rewrite (_3_b_i_A) in *; inversion H1.
    (* destruct H2. *)
    rewrite ->  H8 in *.
    clear o H8.
    rename r into o. (* it couldn't do it directly *)
    rename c into C'.
    clear H1.

    apply inr.
    exists (C', o).
    exists x2.
    split.
    apply p_env.updatedFuncProp; apply eq_refl.
    split.

    set (lem := proj1 (p_gamma.updatedFuncProp gamma  x sigma0 x) (eq_refl x)).
    rewrite lem in H0; inversion H0. rewrite H6 in *.
    rename sigma1 into sigma'; clear  H6 H0.
    rewrite H2 in H5; inversion H5; rewrite <- H1 in *.
    clear H1 H5.
    exact lem.
    exact H4.

    (* 3 c, L(y) = b(o)*)
    rename H10 into _3_c.
    rename r into o.
    destruct X2 as [_3_c_i_A _3_c_i_B].
    clear Gamma.
    rename H5 into _1_b.
    rename sigma0 into sigma'.
    simpl in wf_var_y.

    rename wf_var_y into _3_c_ii.
    induction (_3_c_ii).
    induction a. (* 3. c. iii. *)
    rewrite a in _3_c; discriminate. (* 3. c. iv.*)
    induction b; destruct x2; destruct p; destruct a.
    rename H1 into _3_c_v.
    rewrite _3_c_v in _3_c; discriminate. (* 3. c. v. *)

    

    destruct b; destruct x2. destruct y0; destruct a; destruct H2.
    rewrite _3_c in H1; inversion H1.
    rename x0 into z.
    rename sigma1 into tau.
    intro.

    assert (p_gamma.func Gamma z = Some tau) as _4_a.
    rewrite <- H0.
    symmetry.
    apply p_gamma.updatedFuncProp. firstorder.

    destruct X2 as [ _4_c_i _4_c_ii].
    set (_4_d := _4_c_ii z tau _4_a).
    unfold WF_Var.
    rewrite H0.
    Require Import Coq.Lists.List.
    assert (In z (p_gamma.domain Gamma)) as _4_ca.
    set (lem := p_gamma.fDomainCompat Gamma z).
    set (in_or_not := in_dec v_eq_dec z (p_gamma.domain Gamma)).
    firstorder; rewrite H1 in _4_a; discriminate.

    set (lem''' := _4_c_i z _4_ca).
    case_eq (p_env.func L z).
    intros envVar _4_ca_ii.

    assert (p_env.func (p_env.updatePartFunc L x null_ref_box ) z = Some envVar) as _4_cb.
    transitivity (p_env.func L z).
    apply p_env.updatedFuncProp. firstorder.
    exact _4_ca_ii.
    unfold WF_Var in _4_d.
    rewrite _4_cb in *.
    rewrite _4_ca_ii in _4_d.
    rewrite _4_a in _4_d.
    exact _4_d.

    intro.
    set (lem'''':= proj2 (p_env.fDomainCompat L z ) H1).
    firstorder.

    (* Case t = let y = Null in t' *)
    rewrite  H9 in *; clear H9 e0 t H6.
    rewrite <- H8 in *; clear H8.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H5 in *; clear e H5.
    rewrite <- H4 in *; clear H4.
    clear H3 H1 L0 H0.
    clear L'.
    rename t' into t.

    rename X into asm1.
    rename X0 into asm0.
    clear H2 . 

    clear v.

    inversion asm1.
    clear sigma0 ann0 H3 H5 t0 H4 H1 L0 H0 H2.

    rename X0 into _3_b.
    rename X into _3_a.
    inversion _3_a.

    clear H2 tau t0 H5 e H4 x0 H3 eff0 H1 H0 gamma.
    rename sigma0 into sigma'.
    rename X into _4_a.
    rename X0 into _4_b.

    destruct _3_b as [_6_a _6_b].

    apply (t_frame1 H (p_gamma.updatePartFunc Gamma x sigma' )
                    eff t
                    (p_env.updatePartFunc L x envNull) ann sigma).
    simpl in H6.
    exact  (proj2 H6).
    exact _4_b.

    unfold WF_Env.
    split.
    
    exact (subset_preserved Gamma L x sigma' envNull _6_a).

    intros z tau _8.
    elim (v_eq_dec x z).
    intro x_is_z; rewrite <- x_is_z in *; clear x_is_z.
    