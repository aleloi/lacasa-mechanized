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


Section Progress.

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

  Print sfconfig_type.
  Print ann_frame.

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
    

End Progress.