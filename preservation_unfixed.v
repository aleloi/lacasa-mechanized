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


Section Preservation_fix.

  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  Definition t_frame1' := t_frame1 P.
  Definition WF_Frame' := WF_Frame P.

  Definition Reduction_SF' := Reduction_SF P .
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecksTerm P.
  Definition TypeChecksExprP := TypeChecksExpr P.
  Definition Heap_okP := Heap_ok P.
  Definition Heap_dom_okP := Heap_dom_ok P .
  

  Require Import Coq.Lists.List.

  Notation "( p +++ a ↦ b )" := (p_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o ↦ obj )" := (p_heap.updatePartFunc
                                     H o obj)
                                    (at level 0).
  Notation "( Γ ⊍ x ↦ σ )" := (p_Γ.updatePartFunc
                                     Γ x σ)
                                (at level 0).
  Notation " a ⪳ b " := (subtype P a b) (at level 0).
  Notation " a ⪯ b " := (subclass P a b) (at level 0).

  Notation "[ L , t ] ^ a" := (ann_frame (sframe L t) a) (at level 0).

  Notation "y ∘ f ⟵ z" := (FieldAssignment y f z) (at level 0).

  Notation "a ⟿ b" :=  (Reduction_SF' a b) (at level 0).
  Notation " ⊢ H" := (Heap_okP H) (at level 0).
  Notation " ⊩ H" := (Heap_dom_okP H) (at level 0).
  Notation "( Γ , ef ⊩' t ▷ σ )" := (TypeChecksTerm P Γ ef t σ) (at level 0).
  Notation "( Γ , ef ⊩'' e ▷ σ )" := (TypeChecksExpr P Γ ef e σ) (at level 0).

  Notation "a ∉ lst" := (~ (In a lst)) (at level 0).
    

  Theorem preservation_case_box :
    forall H L σ ann t C x o flds,
      WF_Frame' H (ann_frame (sframe L t_let x <- Box C t_in (t)) ann) σ ->
      Heap_okP H ->
      ~ In o (p_heap.domain H) ->
      fieldsP C flds ->
      WF_Frame'
        (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))
        (ann_frame (sframe (p_env.updatePartFunc L x (envBox o)) t) ann) σ.
   Admitted.
  
    Theorem preservation_case_select :
    forall H L σ ann x y f t C FM fmVal o,
      WF_Frame' H (ann_frame (sframe L t_let x <- FieldSelection y f t_in (t)) ann) σ ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_FM.func FM f = Some fmVal ->
      WF_Frame'
        H
        (ann_frame (sframe (p_env.updatePartFunc L x (fm2env fmVal)) t) ann) σ.
    intros.

    (* 2 *)
    rename H1 into t_typ_σb.
    rename H2 into _2_cd.
    rename H3 into _2_e.
    rename H4 into t_is_term.
    rename H0 into _2_j.
    rename X into _2_k.

    (* 3 *)
    inversion _2_k.
    clear H3 sigma0 H5 ann0 H4 H1 H2.
    rename X into ΓL_sub.
    rename X0 into wf_vars.


    (* 4 *)
    inversion ΓL_sub.
    clear tau H3 H7 t1 H5 e H4 x0 eff0 H2.
    rewrite <- H1 in * ; clear H1 Gamma.
    inversion X.
    clear H5 f0 H1 x0 eff0 H3 gamma0 H2.
    rename C0 into D.
    rename H7 into typ_newC.
    rename witn into typ_next_frame.
    set (E := ftype P D f typ_next_frame).
    rewrite <- H4 in *.
    fold E in X, X0.
    clear H4.
    (* rename H4 into _4_c. *)
    rename X0 into _4_d.
    rename X into _4_e.
    set (L' := p_env.updatePartFunc L x (fm2env fmVal)).
    clear t0 L0 H0.


    (* 5 *)
    set (Gamma' := p_gamma.updatePartFunc gamma x (typt_class E)).
    fold Gamma' in _4_d.
    
    (* 6 *)
    inversion wf_vars.
    rename H0 into wf_vars_i.
    rename X into wf_vars_ii.
    set (_6 := subset_preserved gamma L x (typt_class E) (fm2env fmVal)  wf_vars_i).


    (* OTHER ORDER COMPARED TO paper proof*)
    clear H6 sigma0.
    apply (t_frame1 P _ Gamma' eff _ _ _ _ t_is_term _4_d).
    split.
    apply _6.
    intros z tau.

    (* END OTHER *)

    case_eq (v_eq_dec x z).
    (* 7 *)
    (* 7 a *)
    intros.
    rewrite <- e in *; clear e z.
    clear H0.
    assert (p_env.func L' x = Some (fm2env fmVal)) as gamma_L_subset_a.
    unfold L'.
    rewrite  ( proj1 (p_env.updatedFuncProp L x (fm2env fmVal) x) (eq_refl x)).
    reflexivity.
    
    assert (p_gamma.func Gamma' x = Some (typt_class E)) as gamma_x_E.
    unfold Gamma'.
    rewrite  ( proj1 (p_gamma.updatedFuncProp gamma x (typt_class E) x) (eq_refl x)).
    reflexivity.
    clear H1.

    (* 7 b *)
    induction fmVal; unfold fm2env in gamma_L_subset_a.
    
    (* 7 b i *)
    apply inl. apply inl.
    exact gamma_L_subset_a.

    (* 7 c *)
    rename r into o'.
    set (test := _2_j o C FM _2_cd f o').
    
    apply inl.  apply inr.
    exists (E, o').
    unfold Gamma'.
    assert (subclass P C D) as C_sub_D.
    
    induction ( wf_vars_ii y (typt_class D) typ_newC).
    induction a.
    rewrite  t_typ_σb in a; discriminate a.
    destruct b.
    destruct x0.
    destruct y0.
    destruct a.
    destruct H1.
    rewrite t_typ_σb in H0.
    inversion H0.
    rewrite H4 in *.
    rewrite typ_newC in H1.
    inversion H1.
    rewrite <- H5 in *.
    clear c H5.
    assert (heap_typeof H r x0 = C).
    unfold heap_typeof.
    (* TODO: rewriting *)
    admit.
    (* rewrite <- H4. *)
    (* rewrite _2_cd. *)
    (* reflexivity. *)
    rewrite H3 in H2.
    inversion H2.
    exact H7.
    destruct b.   destruct x0. 
    destruct y0.
    destruct a.
    rewrite t_typ_σb in H0.
    inversion H0.
    
    assert (fld P C f) as f_field_C.
    apply (field_subclass P C D  _  typ_next_frame).
    
    exact C_sub_D.
    destruct (test f_field_C _2_e).
    clear test.
    exists x0.
    split.
    exact gamma_L_subset_a.
    split.
    exact gamma_x_E.
    
    (*  *)
    (*
     * know: Gamma' x = E
     * typeof(H, o') <: ftype(C, f)
     * --------------
     * ftype(C, f) = E
     * --------------------- 
     * Goal:  heapof(H, o') <: E
     *
     *)
    apply classSub.
    assert (E = heap.ftypeP P C f f_field_C).
    unfold E.
    unfold heap.ftypeP.
    rewrite (unique_ftype P C f f_field_C (field_subclass P C D f f_field_C C_sub_D)).
    rewrite <- (ftype_subclass P C D f f_field_C C_sub_D).
    apply (unique_ftype P D f _ _).
    rewrite <- H0 in s.
    exact s.

    (* 8 *)
    intros.
    clear H0.

    (* 8 a b *)
    assert (p_gamma.func gamma z = Some tau).
    rewrite <- H1.
    symmetry.
    set (lem := proj2 (p_gamma.updatedFuncProp gamma x (typt_class E) z)).
    firstorder.
    rename H0 into _8_b.
    assert (In z (p_gamma.domain gamma)) as _8_a.
    apply (p_gamma.in_part_func_domain _ z tau _8_b).

    (* 8 c *)
    assert (In z (p_env.domain L)) as _8_c.
    apply (wf_vars_i _ _8_a).

    set (_8_e_i := wf_vars_ii z tau _8_b).
    unfold WF_Var.

    assert (p_env.func L z = p_env.func L' z) as _8_d.
    set (lem := proj2 (p_env.updatedFuncProp L x (fm2env fmVal) z)).
    symmetry. firstorder.
    rewrite <- _8_d.
    rewrite <- _8_b in H1.
    rewrite H1.
    exact _8_e_i.
  Admitted.


    Theorem preservation_case_assign H L x y f z t C FM o σ envVal ann:
    forall witn: is_not_box envVal,
      WF_Frame' H (ann_frame (sframe L t_let x <- (FieldAssignment y f z) t_in (t)) ann) σ ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_env.func L z = Some envVal ->
      (* isTerm t -> *)
      (WF_Frame'
         (p_heap.updatePartFunc H o
                                (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))
         (ann_frame (sframe (p_env.updatePartFunc L x envVal ) t) ann) sigma) *
      (Heap_okP (p_heap.updatePartFunc H o
                                       (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))
      ).

    (* 1 *)
    intros.
    rename H0 into _1_b.
    rename X into _1_c.

    (* 2 *)
    set (L' := (p_env.updatePartFunc L x envVal)).
    set (FM' := (p_FM.updatePartFunc FM f (env2fm envVal witn))).
    set (H' := (p_heap.updatePartFunc H o (obj C FM'))).
    split.

    (* 2b, L z = o_z or L_z = null*)
    assert ({o_z | envVal = envRef o_z} + (envVal = envNull)) as wf_H_Γ_L.
    case_eq envVal.
    intros.
    apply inr.
    reflexivity.
    intros.
    apply inl.
    exists r.
    reflexivity.
    intros.
    rewrite H0 in *.
    inversion _1_c.
    inversion X.
    inversion X1.

    (* L z = b(r), show Gamma z must be Box[D] *)

    inversion X0.
    set (lem := X4 z _ H23).
    inversion lem.
    destruct X5.
    rewrite e0 in H3.
    simplify_eq H3.
    destruct s.
    destruct x2.
    destruct y1.
    destruct a.
    rewrite H26 in H3.
    simplify_eq H3.

    destruct X5.
    destruct x2.
    destruct y1.
    destruct a.
    destruct H27.
    rewrite H23 in H27 .
    simplify_eq H27.

    rename o into o_y.
    rename H1 into _2_c.
    rename H2 into _2_d.

    (* 2 e says that f in fields(C) by reduction rules (this is wrong!)*)

    (* 3 *)
    inversion _1_c.
    clear H0 H2 t0 H5 ann0 H6 sigma0 H4 L0 H1.
    rename X into ΓL_sub.
    rename X0 into wf_vars.

    (* 4 *)
    inversion ΓL_sub.
    inversion X.
    clear y0 H13 f0 H9 x1 H8 eff1 H11 gamma0 H10.
    unfold typing.subtypeP in *.
    fold TypeChecksP in *.
    fold subtypeP in *.
    unfold typing.fldP in *.
    fold fldP in *.
    clear H2 tau.

    clear x0 H4.
    clear t0 H6.
    clear H1 eff0.
    clear e H5.
    clear gamma H0.
    rewrite <- H12 in *.
    clear sigma0 H12.
    inversion X1.
    clear eff0 H2 x0 H0 H5 f0 gamma H1.
    set (typ_newC := p_gamma.in_part_func_domain Gamma y (typt_class C1) H4).
    set (typ_next_frame := p_gamma.in_part_func_domain Gamma z (typt_class C0) H14).
    rename X1 into _4_c.

    (* unfold subtypeP in H15. *)
    rename H15 into _4_d.
    set (Gamma' := p_gamma.updatePartFunc Gamma x (typt_class C0)).
    fold Gamma' in X0.
    rename X0 into _4_e.

    clear witn2.
    rename C0 into D''.
    rename C into C'.
    rename C1 into C.
    rename H6 into _4_f.

    (* 5 *)
    inversion wf_vars.
    rename H0 into _5_a.
    rename X0 into _5_b.

    (* 6 *)

    apply (t_frame1 _ _ Gamma' eff).
    inversion H7.
    exact H1.
    exact _4_e.
    split.
    exact (subset_preserved _ _ _ _  _  _5_a).

    intros s.
    case_eq (v_eq_dec s x).
    intros.
    clear H0; rewrite -> e in *; clear e s.
    clear sigma0 H1.
    assert (p_gamma.func Gamma' x = p_gamma.func Gamma z ) as _6_a.
    set (lem := proj1 (p_gamma.updatedFuncProp Gamma x (typt_class D'') _) (eq_refl _)).
    fold Gamma' in lem.
    transitivity (Some (typt_class D'')).
    exact lem.
    symmetry.
    exact H14.

    assert (p_env.func L' x = p_env.func L z) as _6_b.
    transitivity (Some envVal).
    exact (proj1 (p_env.updatedFuncProp L x envVal _) (eq_refl _)).
    symmetry.
    exact H3.
    case_eq wf_H_Γ_L.
    intros.
    clear H0 wf_H_Γ_L.
    destruct s.
    rewrite -> e in *.
    rename x0 into o_z.
    assert (In o_z (p_heap.domain H)).
    destruct (_5_b z (typt_class D'') H14).
    destruct s.
    rewrite e0 in H3.
    inversion H3.
    destruct s. destruct x0.
    destruct y0.
    destruct a.
    rewrite H0 in H3.
    inversion H3.
    rewrite <- H5 in *.
    exact x0.
    destruct s.
    destruct x0.
    destruct y0.
    destruct a.
    rewrite H0 in H3; inversion H3.
    set (stays := p_heap.staysInDomain H o_y (obj C' FM') o_z H0).
    assert (heap_typeof H' o_z stays = heap_typeof H o_z H0) as _6_iv.
    case_eq (rn_eq_dec o_z o_y).
    intros.
    clear H1; rewrite e0 in *.
    transitivity C'.
    unfold heap_typeof.
    assert (p_heap.func H' o_z = Some (obj C' FM')).
    rewrite e0.
    unfold H'.
    exact (proj1 (p_heap.updatedFuncProp H o_y (obj C' FM') _) (eq_refl _)).

    (* TODO: rewrite *)
    admit.
    (* rewrite H1. *)
    (* reflexivity. *)
    symmetry.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit.
    (* rewrite e0. *)
    (* rewrite _2_d. *)
    (* reflexivity. *)
    intros.
    clear H1.
    set (lem := proj2 (p_heap.updatedFuncProp H o_y (obj C' FM') _) n).
    fold H' in lem.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite lem. *)
    (* reflexivity. *)
    unfold WF_Var.
    apply inl.
    apply inr.
    rewrite _6_b.
    rewrite _6_a.
    exists (D'', o_z).
    exists stays.
    split.
    exact H3.
    split.
    exact H14.
    rewrite _6_iv.
    unfold wf_env.subtypeP.
    (* apply classSub. *)
    elim (_5_b z (typt_class D'') H14).
    intro.
    destruct a.
    rewrite e0 in H3; inversion H3.
    destruct s.
    destruct x0.
    destruct y0.
    destruct a.
    rewrite H1 in H3; inversion H3.
    rewrite H6 in *.
    destruct H2.
    rewrite H14 in H2; inversion H2.
    rewrite <- H9 in *.
    rewrite <- H6 in *.
    (* dependent rewrite H6 in x0. *)
    assert ((heap_typeof H r x0) = (heap_typeof H o_z H0)).
    case_eq (p_heap.func H r).
    intros.
    destruct b.
    transitivity c0.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite H8. *)
    (* reflexivity. *)
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite <- H6. *)
    (* rewrite H8. *)
    (* reflexivity. *)
    intros.
    elim (proj2 (p_heap.fDomainCompat H r) H8 x0).
    rewrite <- H8.
    exact H5.
    rename _6_iv into _6_d_iv.

    (* 6 e *)
    intros.
    destruct b.
    destruct x0.
    destruct y0.
    destruct a.
    destruct H2.
    rewrite H14 in H2; discriminate H2.

    (* L z = null *)
    intros.
    clear H0.
    rewrite e in *.
    apply inl.
    apply inl.
    rewrite _6_b.
    assumption.


    (* 7 a *)
    intros gamma_L_subset dummy tau gamma_L_subset';    clear dummy.
    assert (p_gamma.func Gamma' s = p_gamma.func Gamma s) as gamma_L_subset_a.
    apply (proj2 (p_gamma.updatedFuncProp _ _ _ _) gamma_L_subset).
    assert (p_env.func L' s = p_env.func L s) as gamma_L_subset_b.
    apply (proj2 (p_env.updatedFuncProp _ _ _ _) gamma_L_subset).
    rewrite gamma_L_subset' in gamma_L_subset_a.
    symmetry in gamma_L_subset_a.
    set (gamma_L_subset_c := _5_b s tau gamma_L_subset_a).

    case_eq (p_env.func L s).
    intros.
    case_eq b.
    intros.
    apply inl. apply inl.
    rewrite H1 in H0.
    rewrite H0 in gamma_L_subset_b.
    assumption.

    (* 7 e, b = envRef o_s *)
    clear _1_c.
    clear ann.
    intros.
    rename r into o_s.
    rewrite H1 in *.
    destruct gamma_L_subset_c. (* case analysis on WF-var Gamma L s *)
    destruct s0.
    rewrite H0 in e; discriminate e.
    destruct s0.
    destruct x0; destruct y0; destruct a; destruct H5.
    rewrite H2 in H0;    inversion H0.
    rewrite <- H9 in *; clear H9.
    clear o_s; rename r into o_s.
    clear H0 b H1.
    rename H5 into gamma_L_subset_e_i.
    rename c into G.
    rename H6 into gamma_L_subset_e_ii.
    set (stays := p_heap.staysInDomain H o_y (obj C' FM') o_s x0).
    fold H' in stays.

    (* 7 e iii *)
    assert (heap_typeof H o_s x0 = heap_typeof H' o_s stays) as gamma_L_subset_e_iii.
    case_eq (rn_eq_dec o_s o_y).
    intros.
    clear H0. rewrite <- e in *.
    transitivity C'.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit.
    (* rewrite _2_d; reflexivity. *)
    
    unfold heap_typeof.
    assert (p_heap.func H' o_y = Some (obj C' FM')).
    unfold H'.
    exact (proj1 (p_heap.updatedFuncProp H o_y (obj C' FM') _) (eq_refl _)).

    (* TODO: rewrite *)
    admit. 
    (* rewrite e. *)
    (* rewrite H0. *)
    (* reflexivity. *)
    intros.
    clear H0.
    
    set (lem := proj2 (p_heap.updatedFuncProp H o_y (obj C' FM') _) n).
    fold H' in lem.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite lem. *)
    (* reflexivity. *)
    (* end 7 e iii *)
    
    set (lem := _5_b s tau gamma_L_subset_a).
    unfold WF_Var.
    rewrite gamma_L_subset_b.
    rewrite gamma_L_subset'.

    (* Case analysis L s = null / o / box with H |- Gamma L s
     * leads to Gamma s = G, typeof(H, o_s) <: G
     *)
    destruct lem.
    destruct s0.
    apply inl. apply inl. assumption.
    apply inl.
    apply inr.
    destruct s0.
    destruct x1.
    exists (c, r).
    destruct y0.
    destruct a.
    rewrite H0 in H2; inversion H2.
    rewrite H6 in *.
    assert (In o_s (p_heap.domain H')).
    assumption.
    exists H5.
    split.
    assumption.
    split.
    destruct H1.
    rewrite H1 in gamma_L_subset_a.
    symmetry.
    assumption.
    assert ((heap_typeof H r x1) = (heap_typeof H' o_s H5)).
    transitivity (heap_typeof H o_s x0).
    case_eq (p_heap.func H r).
    intros.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite H8. *)
    (* rewrite H6 in H8. *)
    (* rewrite H8. *)
    (* reflexivity. *)
    intros.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite H8. *)
    (* rewrite H6 in H8. *)
    (* rewrite H8. *)
    (* assumption. *)

    case_eq (rn_eq_dec o_s o_y).
    intros.
    clear H8. 
    transitivity C'.
    unfold heap_typeof.
    rewrite e in *.

    (* TODO: rewrite *)
    admit. 
    (* rewrite _2_d. reflexivity. *)
    unfold heap_typeof.
    assert (p_heap.func H' o_y = Some (obj C' FM')).
    unfold H'.
    exact (proj1 (p_heap.updatedFuncProp H o_y (obj C' FM') _) (eq_refl _)).

    (* TODO: rewrite *)
    admit. 
    (* rewrite e. *)
    (* rewrite H8. *)
    (* reflexivity. *)
    intros.
    clear H8.
    
    set (lem := proj2 (p_heap.updatedFuncProp H o_y (obj C' FM') _) n).
    fold H' in lem.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite lem. *)
    (* reflexivity. *)
    
    rewrite <- H8.
    destruct H1.
    exact H9.
    
    destruct s0.
    destruct x1.
    destruct y0.
    destruct a.
    destruct H1.
    rewrite H0 in H2; inversion H2.

    destruct s0.
    destruct x0; destruct y0. destruct a. destruct H5.
    rewrite H2 in H0; discriminate H0.
    (* END 7 e!!! *)

    intros.
    rename r into o_s.
    rewrite H1 in *.

    (* Case analysis on H |- Gamma ; L ; s to get box prop: *)
    set (lem := _5_b s tau gamma_L_subset_a).
    destruct lem.
    destruct s0.
    rewrite e in H0; discriminate H0.
    destruct s0; destruct x0; destruct y0; destruct a.
    rewrite H2 in H0; discriminate H0.
    destruct s0; destruct x0; destruct y0; destruct a; destruct H5.
    rewrite H2 in H0; simplify_eq H0.
    intro equRef; rewrite equRef in *.
    clear H0.
    rewrite gamma_L_subset_a in H5; simplify_eq H5.
    intro equTy; rewrite equTy in *.
    rename c into F.
    rename gamma_L_subset' into gamma_L_subset_f_i_A.
    assert (In o_s (p_heap.domain H)).
    rewrite <- equRef.
    assumption.
    assert (In o_s (p_heap.domain H')).
    unfold H'.
    apply (p_heap.staysInDomain H _ _ o_s).
    assumption.
    assert (heap_typeof H o_s H0  = heap_typeof H' o_s H8) as gamma_L_subset_f_ii.

    case_eq (rn_eq_dec o_s o_y).
    intros.
    rewrite e in *.
    clear H9.
    transitivity C'.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite e. *)
    (* rewrite _2_d. *)
    (* reflexivity. *)

    
    unfold heap_typeof.
    assert (p_heap.func H' o_y = Some (obj C' FM')).
    apply (p_heap.updatedFuncProp _ _ _ _).
    reflexivity.

    (* TODO: rewrite *)
    admit. 
    (* rewrite e. *)
    (* rewrite H9. *)
    (* reflexivity. *)
    
    intros.
    clear H9.
    case_eq (p_heap.func H o_s).
    intros.
    destruct b0.
    transitivity c.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit.
    (* rewrite H9. *)
    (* reflexivity. *)

    
    assert (p_heap.func H' o_s = Some (obj c f0)).
    unfold H'.
    transitivity  (p_heap.func H o_s).
    apply (proj2 (p_heap.updatedFuncProp H o_y (obj C' FM') o_s) ).
    assumption.
    assumption.
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite H10. *)
    (* reflexivity. *)

    intros.
    elim (proj2 (p_heap.fDomainCompat H o_s) H9 H0).
    unfold WF_Var.
    rewrite gamma_L_subset_b.
    rewrite gamma_L_subset_f_i_A.
    rewrite H2.
    apply inr.
    exists (F, o_s).
    exists H8.
    split.
    reflexivity.
    split.
    reflexivity.
    rewrite <- gamma_L_subset_f_ii.
    assert ((heap_typeof H o_s H0) = (heap_typeof H r x0)
           ).
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite equRef. *)
    (* induction (p_heap.func H o_s); *)
    (* reflexivity. *)
    
    rewrite H9.
    assumption.

    intro.
    set (s_in_gamma := p_gamma.in_part_func_domain Gamma s tau gamma_L_subset_a).
    set (lem := _5_a _ s_in_gamma).
    elim (proj2 (p_env.fDomainCompat _ _) H0 lem).

    (* HEAP OK *)

    intro.
    rename o into o_y.
    rename o0 into o.

    case_eq (rn_eq_dec o_y o).
    intros; clear H0.
    rewrite <- e in *.
    set (lem := proj1 (p_heap.updatedFuncProp H o_y (obj C FM') _) (eq_refl _)).
    fold H' in lem.
    rewrite lem in H4.
    inversion H4.
    rewrite <- H5 in *.
    rewrite <- H6 in *.
    clear H5 H6 C0 FM0.
    clear lem H4 e o.
    intro; intros.
    
    case_eq (fn_eq_dec f0 f).
    intros.
    clear H4; rewrite e in *.
    set (lem := proj1 (p_FM.updatedFuncProp FM f (env2fm envVal witn) f) (eq_refl _ )).
    fold FM' in lem.
    rewrite H0 in lem.
    inversion lem.
    induction envVal; 
    inversion H5.
    rewrite <- H6 in *.
    rename o into o_z.
    rename H3 into _9_b_ii_B.
    rename H0 into _9_b_ii_A.
    
    inversion _1_c.
    destruct X0.
    inversion X.
    inversion X0.
    set (_9_b_iii_lem := w z (typt_class C0) H23).
    unfold WF_Var in _9_b_iii_lem.
    assert ({C_o : class * Ref_type |
             let (C, o) := C_o in
             {witn : In o (p_heap.domain H) |
              p_env.func L z = Some (envRef o) /\
              p_gamma.func Gamma z = Some (typt_class C) /\
              wf_env.subtypeP P (typt_class (heap_typeof H o witn))
                              (typt_class C)}}).
    induction _9_b_iii_lem.
    induction a.
    rewrite a in _9_b_ii_B; simplify_eq _9_b_ii_B.
    exact b.
    destruct b; destruct x2; destruct y1; destruct a.
    rewrite H25 in _9_b_ii_B; simplify_eq _9_b_ii_B.
    clear _9_b_iii_lem.

    destruct X3; destruct x2; destruct y1; destruct a.
    rewrite H25 in _9_b_ii_B; simplify_eq _9_b_ii_B.
    intro ref_eq; rewrite ref_eq in *.
    destruct H26.
    rename H26 into _9_b_v_C.
    rename H27 into _9_b_v_D.
    rename H25 into _9_b_v_A.
    assert (In o_z (p_heap.domain H)) as _9_b_v_B.
    rewrite <- ref_eq; assumption.
    rewrite _9_b_v_C in H23; simplify_eq H23; intro simpl_eq; rewrite simpl_eq in *.
    inversion X2.

    set (lemlem := w y (typt_class C1) H28).
    
    assert ({C_o : class * Ref_type |
           let (C, o) := C_o in
           {witn : In o (p_heap.domain H) |
           p_env.func L y = Some (envRef o) /\
           p_gamma.func Gamma y = Some (typt_class C) /\
           wf_env.subtypeP P (typt_class (heap_typeof H o witn))
                           (typt_class C)}}).
    induction lemlem.
    induction a.
    rewrite a in H1; simplify_eq H1.
    assumption.

    destruct b; destruct x4; destruct y1; destruct a; destruct H32.
    rewrite H32 in H28; simplify_eq H28.
    destruct X3.
    destruct x4.
    destruct y1.
    destruct a.
    destruct H32.
    rewrite H31 in H1; simplify_eq H1; intro equu; rewrite equu in *.
    rewrite H28 in H32; simplify_eq H32; intro equuu; rewrite <- equuu in *.
    assert (heap_typeof H r1 x4 = C).
    unfold heap_typeof.

    (* TODO: rewrite *)
    admit. 
    (* rewrite equu. *)
    (* rewrite H2. *)
    (* reflexivity. *)
    
    rewrite H34 in H33.

    assert ((heap.ftypeP P C f f_witn) = D).
    rewrite <- H30.
    symmetry.
    inversion H33.
    apply (ftype_subclass _ _ _ _ _ H37).
    rewrite H35.

    exists (p_heap.staysInDomain H o_y (obj C FM') o_z _9_b_v_B).
    assert ((heap_typeof H' o_z
                         (p_heap.staysInDomain H o_y (obj C FM') o_z _9_b_v_B))
            = (heap_typeof H o_z _9_b_v_B)
           ).
    unfold heap_typeof.
    case_eq (rn_eq_dec o_z o_y).
    intros.


    (* TODO: rewrite *)
    admit. 
    (* rewrite e1. *)
    (* assert (p_heap.func H' o_y = Some (obj C FM')). *)
    (* apply (p_heap.updatedFuncProp). *)
    (* reflexivity. *)
    (* rewrite H37. *)
    (* rewrite H2. *)
    (* reflexivity. *)
    
    intros.
    assert (p_heap.func H' o_z = p_heap.func H o_z).
    apply (p_heap.updatedFuncProp).
    assumption.

    (* TODO: rewrite *)
    admit. 
    (* rewrite H37. *)
    (* induction (p_heap.func H o_z). *)
    (* reflexivity. *)
    Admitted.
  (*   reflexivity. *)
  (*   rewrite H36. *)

  (*   assert ((heap_typeof H o_z _9_b_v_B) = (heap_typeof H r0 x2)). *)
  (*   unfold heap_typeof. *)
  (*   rewrite ref_eq. *)
  (*   induction (p_heap.func H o_z). *)
  (*   reflexivity. *)
  (*   reflexivity. *)
  (*   rewrite H37. *)
  (*   inversion _9_b_v_D. *)
  (*   apply (subclass_trans P (heap_typeof H r0 x2) C0 D). *)
  (*   assumption. *)
  (*   inversion H24. *)
  (*   assumption. *)
  (*   inversion witn. *)

  (*   intros. *)
  (*   clear H4. *)

  (*   assert (p_FM.func FM' f0 = p_FM.func FM f0). *)
  (*   apply (p_FM.updatedFuncProp). *)
  (*   assumption. *)
  (*   rewrite H0 in H4. symmetry in H4. *)
  (*   set (lem := _1_b o_y C FM H2 f0 o f_witn H4). *)
  (*   destruct lem. *)
  (*   exists (p_heap.staysInDomain H o_y (obj C FM') o x0). *)

  (*   assert ((heap_typeof H' o (p_heap.staysInDomain H o_y (obj C FM') o x0)) *)
  (*           = (heap_typeof H o x0) *)
  (*          ). *)

  (*   case_eq (rn_eq_dec o o_y). *)
  (*   intros. *)
  (*   clear H5. *)
  (*   unfold heap_typeof. *)
  (*   rewrite e. *)
  (*   assert (p_heap.func H' o_y = Some (obj C FM')). *)
  (*   apply (p_heap.updatedFuncProp). *)
  (*   reflexivity. *)
  (*   rewrite H5. *)
  (*   rewrite H2. *)
  (*   reflexivity. *)
  (*   intros . *)
  (*   unfold heap_typeof. *)
  (*   assert (p_heap.func H' o = p_heap.func H o). *)
  (*   apply (p_heap.updatedFuncProp). *)
  (*   assumption. *)
  (*   rewrite H6. *)
  (*   induction (p_heap.func H o); *)
  (*     reflexivity. *)
  (*   rewrite H5. *)
  (*   assumption. *)

  (*   intros. *)
  (*   assert (p_heap.func H' o = p_heap.func H o). *)
  (*   apply (p_heap.updatedFuncProp). *)
  (*   firstorder. *)
  (*   case_eq (p_heap.func H o). *)
  (*   intros. *)
  (*   destruct b. *)
  (*   rewrite H5 in H4. *)
  (*   rewrite H6 in H4. *)
  (*   inversion H4. *)
  (*   rewrite H8, H9 in *. *)
  (*   clear H4 H8 H9 c f0. *)
  (*   intro; intros. *)
  (*   set (lem := _1_b o C0 FM0 H6 f0 o0 f_witn H4). *)
  (*   destruct lem. *)
  (*   exists (p_heap.staysInDomain H o_y (obj C FM') o0 x0). *)
  (*   assert ((heap_typeof H o0 x0) = (heap_typeof H' o0 (p_heap.staysInDomain H o_y (obj C FM') o0 x0))). *)
  (*   case_eq (rn_eq_dec o0 o_y). *)
  (*   intros. *)
  (*   unfold heap_typeof. *)
  (*   rewrite e. *)
  (*   rewrite H2. *)
  (*   assert (p_heap.func H' o_y = Some (obj C FM')). *)
  (*   apply (p_heap.updatedFuncProp). *)
  (*   reflexivity. *)
  (*   rewrite H8. *)
  (*   reflexivity. *)
  (*   intros. *)
  (*   unfold heap_typeof. *)
  (*   assert (p_heap.func H o0 = p_heap.func H' o0). *)
  (*   symmetry. *)
  (*   apply (p_heap.updatedFuncProp). *)
  (*   assumption. *)
  (*   rewrite H8. *)
  (*   induction (p_heap.func H' o0); *)
  (*     reflexivity. *)
  (*   rewrite <- H7. *)
  (*   assumption. *)
  (*   intros. *)
  (*   rewrite H6 in H5. *)
  (*   rewrite H5 in H4. *)
  (*   inversion H4. *)


