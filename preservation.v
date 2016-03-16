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

    inversion X0.
    rewrite <- H18 in *; clear H18 H12 H7 H1.
    rewrite <- H19 in *; clear H19 H13 H2.
    rewrite <- H6 in *; rewrite <- H9 in *. clear H20 H17 H9 H6.
    clear H14.
    rewrite <- H5 in *.
    inversion H16.
    rewrite H2 in *; clear H2 H16 H5.
    rewrite <- H4 in *.
    clear H15 H4 v.
    clear L1 H11 t0 y0 x0.
    assert (Some null_ref_box0 = Some null_ref_box). transitivity (p_env.func L y).
    auto. auto.
    inversion H1.
    rewrite H4 in *.
    clear H4 H1 H8 H21 null_ref_box0.

    inversion X.
    clear H6 t0. clear H4 H1. clear L1 H2.
    clear ann0 sigma0 H7 H5.
    clear H' t' e0 e L' H0.
    
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
    rewrite ->  H7 in *.
    clear o H7.
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
    TODO: finish here!
    (* assert (p_gamma.func Gamma z = Some tau) as _4_a. *)
    
    
    (* destruct b; destruct x2. destruct y0; destruct a; destruct H2. *)
    (* rewrite _1_b in H2; inversion H2. *)
    (* rewrite  H6 in *. *)
    (* clear H2. *)
    (* assert (p_gamma.func gamma y = Some (typt_box c)). *)
    (* transitivity (Some sigma'). auto. *)
    (* f_equal. auto. *)
    (* rename H2 into _1_b'. *)
    (* set (_3_c_ii' := _3_c_i_B y (typt_box c) _1_b'). *)
    (* clear _3_c_ii _1_b. *)
    (* rename _1_b' into _3_c_vi_A. *)
    (* rename H4 into _3_c_vi_B. *)
    (* rename _3_c_ii' into _3_c_ii. *)
    (* clear H6 sigma'. *)
    (* rewrite _3_c in H1. *)
    
    
    
    set (_1_b' := )
    rewrite H6 in _3_c_ii.
    
    rewrite <- H7 in *.
    set (test := _3_c_i_B x )
    apply p_gamma.updatedFuncProp; apply eq_refl.
    auto.
