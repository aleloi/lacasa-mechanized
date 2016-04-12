(*
progress: 
 *)
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


Section Progress_SF.

  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  Definition t_frame1' := t_frame1 P.
  Definition WF_Frame' := WF_Frame P.

  Definition Reduction_SF' := Reduction_SF P .
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecks P.
  Definition Heap_okP := Heap_ok P.
  Definition Heap_dom_okP := Heap_dom_ok P .

  Notation "( p +++ a --> b )" := (p_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o --> obj )" := (p_heap.updatePartFunc
                                              H o obj)
                                      (at level 0).

  Theorem progress_SF_case_new :
    forall H L C t x sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- New C t_in (t)))
                     ann) sigma ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, t_let x <- New C t_in (t) !)
                  frame}.
    Proof.
      intros.
      inversion X.
      clear H2 H4 L0 H3 t0 H6 ann0 H7 sigma0 H5.

      (* define flds *)
      set (flds := fieldsList P C).
      set (C_flds := fieldsListIsFields P C).
      fold flds in C_flds.
      set (FM := p_FM.newPartFunc flds FM_null).
            
      destruct (ConcreteNamesAndTypes.rn.constructFresh
                  (p_heap.domain H))
        as [o o_fresh_prop].
      
      exists ( # (H +*+ o --> (obj C FM)),
               ( L +++ x --> envRef o ) , t ! ).
      apply (E_New _ _ _ _ _ _  _ _  flds).
      inversion H8.
      assumption; clear H2 H3.
      assumption.
      assumption.
      reflexivity.
    Qed.

    Theorem progress_SF_case_box :
    forall H L C t x sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- Box C t_in (t)))
                     ann) sigma ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, t_let x <- Box C t_in (t) !)
                  frame}.
    Proof.
      intros.
      inversion X.
      clear H2 H4 L0 H3 t0 H6 ann0 H7 sigma0 H5.

      (* define flds *)
      set (flds := fieldsList P C).
      set (C_flds := fieldsListIsFields P C).
      fold flds in C_flds.
      set (FM := p_FM.newPartFunc flds FM_null).
            
      destruct (ConcreteNamesAndTypes.rn.constructFresh
                  (p_heap.domain H))
        as [o o_fresh_prop].
      
      exists ( # (H +*+ o --> (obj C FM)),
               ( L +++ x --> envBox o ) , t ! ).
      apply (E_Box _ _ _ _ _ _  _ _  flds).
      inversion H8.
      assumption; clear H2 H3.
      assumption.
      assumption.
      reflexivity.
    Qed.


    Theorem progress_SF_case_var :
    forall H L t x y sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- (Var y) t_in t))
                     ann) sigma ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, (t_let x <- (Var y) t_in t) !)
                  frame}.
    Proof.
      intros.
      inversion X.
      clear H2 H4 L0 H3 t0 H6 ann0 H7 sigma0 H5.
      
      assert ({null_ref_box | p_env.func L y = Some null_ref_box}).
      clear H8 H1 H0 X ann.
      inversion X0.
      clear H0 gamma H1 eff0 x0 H3 t0 H5 tau H2 e H4.
      inversion X.
      clear H1 eff0 x0 H4 sigma1 H2 H0 X X2 gamma X0.
      apply fst in X1.
      unfold gamma_env_subset in X1.
      apply (fun f => f y) in X1.
      apply (fun f => f (p_gamma.in_part_func_domain _ _ _ H3)) in X1.
      case_eq (p_env.func L y).
      intros L_y L_y_eq.
      exists L_y; reflexivity.
      intro.
      set (lem := p_env.fDomainCompat L y).
      firstorder.
      
      destruct X2 as [null_ref_box L_y_is_null_ref_box].
      
      exists ( # H , (L +++ x --> null_ref_box) , t ! ).
      apply E_Var.
      inversion H8.
      assumption.
      assumption.
    Qed.

    Theorem progress_SF_case_null :
    forall H L t x sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- Null t_in t))
                     ann) sigma ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, (t_let x <- Null t_in t) !)
                  frame}.
    Proof.
      intros.

      exists (# H, (L +++ x --> envNull), t !).
      apply E_Null.
      
      inversion X.
      clear H2 H4 L0 H3 t0 H6 ann0 H7 sigma0 H5 X0 X1 eff Gamma H1 H0 X ann
      sigma P H L .
      inversion H8.
      assumption.
    Qed.

    Theorem progress_SF_case_field :
    forall H L t x y f sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- (FieldSelection y f) t_in t))
                     ann) sigma ->
      p_env.func L y <> Some envNull ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, (t_let x <- (FieldSelection y f) t_in t) !)
                  frame}.
      intros.
      rename H0 into L_y_not_null.
      rename H2 into heap_dom_ok.
      inversion X.
      inversion H7.
      rename H9 into t_is_term.
      clear H8 H7.
      clear H0 H2  H4 L0 H3 t0 H6 ann0 sigma0 H5 H4.
      assert ({C | p_gamma.func Gamma y = Some (typt_class C)}).
      clear H1  X ann.
      inversion X0.
      clear  H0 gamma H1 eff0 x0 H3 t0 H5 tau H2 e H4 x X0 X2 sigma .
      inversion X.
      clear H0 eff0 x f0 H1 H2  H4 gamma H3 sigma0 X witn t t_is_term f.
      exists C; assumption.
      destruct X2 as [C gamma_y_is_C].

      Require Import Coq.Lists.List.

      assert ({o | p_env.func L y = Some (envRef o) /\
                   In o (p_heap.domain H)
              }).

      destruct X1 as [subset L_gamma_compat].
      unfold gamma_env_subset in subset.
      apply (fun f => f y) in subset.
      apply (fun f => f (p_gamma.in_part_func_domain _ _ _ gamma_y_is_C)) in subset.
      apply (fun f => f y (typt_class C) gamma_y_is_C) in L_gamma_compat.
      
      case_eq (p_env.func L y).
      intros L_y L_y_eq.
      destruct L_y.
      firstorder.
      exists r. split. reflexivity.

      destruct L_gamma_compat.
      destruct s.
      firstorder.
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb].
      rewrite L_y_eq in aaaa.
      inversion aaaa.
      rewrite H2 in *.
      assumption.
      
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct bbbb as [aaaaa bbbbb].
      rewrite gamma_y_is_C in aaaaa.
      discriminate.

      destruct L_gamma_compat.
      destruct s.
      firstorder.
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb].
      rewrite L_y_eq in aaaa; discriminate.

      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct bbbb as [aaaaa bbbbb].
      rewrite gamma_y_is_C in aaaaa.
      discriminate.

      intro.
      set (lem := p_env.fDomainCompat L y).
      firstorder.

      destruct X2 as [o L_y_i_o].

      inversion X0.
      clear tau H3 t0 H6 e H5 x0 H4 eff0 H2 gamma H0 X3.
      inversion X2.
      clear  H5 f0 H0 x0 H3 eff0 H2 gamma.
      clear H4 X2 sigma0.
      rewrite  gamma_y_is_C in H6.
      inversion H6.
      rewrite <- H2 in *.
      clear C0 H2 H6.
      rename C into C'.

      destruct X1 as [_ L_gamma_compat].
      apply (fun f => f y (typt_class C') gamma_y_is_C) in L_gamma_compat.
      destruct L_y_i_o as [L_y_i_o o_in_H].
      assert ({C | heap_typeof H o o_in_H = C /\
                   subclass P C C'
              }).
      
      destruct L_gamma_compat.
      destruct s.
      firstorder.
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct bbbb as [aaaaa bbbbb].
      rewrite gamma_y_is_C in aaaaa.
      inversion aaaaa.
      rewrite <- H2 in *.
      clear H2 aaaaa cc.
      rewrite L_y_i_o in aaaa; inversion aaaa.
      rewrite  H2 in *.
      clear aaaa.
      exists (heap_typeof H oo aaa).
      split.

      set (C := heap_typeof H o o_in_H).
      destruct (heap_typeof_impl P H o C o_in_H (eq_refl _))
        as [FM H_o_value].
      rewrite H2 in H_o_value.
      symmetry.
      apply (heap_typeof_same P _ _ _ FM H_o_value).
      unfold wf_env.subtypeP in bbbbb.
      inversion bbbbb.
      clear D H0 H3      .
      assumption.
      
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct bbbb as [aaaaa bbbbb].
      rewrite gamma_y_is_C in aaaaa.
      discriminate.

      unfold Heap_dom_okP in heap_dom_ok.
      destruct X1 as [C heap_tpe_tmp].
      destruct heap_tpe_tmp as [typeof_o_C C_sub_C'].
      
      destruct (heap_typeof_impl P _ _ _ o_in_H typeof_o_C) as [FM H_o_value].
      
      apply (fun f => f o C FM ) in heap_dom_ok.
      apply (fun f => f H_o_value) in heap_dom_ok.
      unfold heap.fieldsP in heap_dom_ok.

      (* goal: *)
      assert (typing.fldP P C f).
      apply (field_subclass P C C'); assumption.
      
      clear L_gamma_compat X0 C' gamma_y_is_C  witn C_sub_C' X L_y_not_null
            H1   Gamma eff   .

      set (lem := fld_in_flds P C f (p_FM.domain FM) H0 heap_dom_ok).

      assert ({fmVal | p_FM.func FM f = Some fmVal}).
      case_eq (p_FM.func FM f).
      intro fmVal; exists fmVal; reflexivity.
      intro.
      set (lemlem := p_FM.fDomainCompat FM f).
      firstorder.

      destruct X as [fmVal FM_f].
      exists      
      ( # H,
        ( L +++ x --> (fm2env fmVal) ) , t ! ).

      apply (E_Field _ _ _ o _ _ _ _
                     C FM _ t_is_term L_y_i_o H_o_value
                     FM_f
            ).
    Qed.


    Theorem progress_SF_case_assign :
    forall H L t x y f z sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- (FieldAssignment y f z) t_in t))
                     ann) sigma ->
      p_env.func L y <> Some envNull ->
      Heap_okP H ->
      Heap_dom_okP H ->
      { frame : sfconfig_type
                  & Reduction_SF'
                  (# H, L, (t_let x <- (FieldAssignment y f z) t_in t) !)
                  frame}.
    Admitted.

End Progress_SF.