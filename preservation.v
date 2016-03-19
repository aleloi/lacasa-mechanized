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

  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  Definition t_frame1' := t_frame1 P.
  Definition WF_Frame' := WF_Frame P.

  Definition Reduction_SF' := Reduction_SF P.
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecks P.
  Definition Heap_okP := Heap_ok P.
  
  
  
  Theorem preservation_light :
    forall gamma H H' L L' t t' sigma eff,
      Reduction_SF' ( # H, L, t !)
                   ( # H', L', t' !)
      ->
      TypeChecksP gamma eff t sigma ->
      {Gamma' : Gamma_type & TypeChecksP Gamma' eff t' sigma}.
    intros.
    case_eq t; intros;  rewrite H0 in *  ;    clear H0 t; inversion X;
    inversion X0;
    exists (p_gamma.updatePartFunc gamma v sigma0); cbn;
    rewrite H9 in *; auto.
  Qed.

  Local Open Scope type_scope.


  Theorem preservation_case_var :
    forall H L x y t sigma ann envVar,
      WF_Frame' H (ann_frame (sframe L (t_let x <- Var y t_in (t))) ann) sigma ->
      p_env.func L y = Some envVar ->
      isTerm t ->
      WF_Frame' H (ann_frame (sframe (p_env.updatePartFunc L x envVar) t) ann) sigma.
    intros.
    rename H0 into H10.
    rename H1 into H3.

    inversion X.
    clear H5 t0. clear H4 H1 H2 H6 L0 ann0 sigma0 H0. 
    
    inversion X0.
    clear gamma H0 x0 H4 eff0 H1 t0 H6 H2 tau H5 e.
    (* split. *)
    apply (t_frame1' H (p_gamma.updatePartFunc Gamma x sigma0) eff t
                     (p_env.updatePartFunc L x envVar) ann sigma H3).
    exact X3.
    split.
    destruct X1.
    apply (subset_preserved _ _ _ _ _ g).
    intros.
    elim (v_eq_dec x x0).
    intro; rewrite <- a in *; clear a.

    inversion X2.
    clear H6 H4 H1; rewrite <- H2 in *; clear H2 sigma2.
    set (wf_var_y := snd X1 y sigma0 H5).
    
    (* 3.
     *)
    induction envVar.
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

    destruct b; destruct x2; destruct y0; destruct a; destruct H2.

    rewrite (_3_b_i_A) in *; inversion H1.

    (* 3 c, L(y) = b(o)*)
    rename H10 into _3_c.
    rename r into o.
    destruct X1 as [_3_c_i_A _3_c_i_B].
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
    
    (* intro. *)
    (* 3 box *)
    rewrite  H6 in *. clear H6 o. rename r into o.
    clear H1.
    unfold WF_Var.
    rewrite H0.
    apply inr.
    exists (c, o).
    exists x2.
    split.
    simpl.
    exact (proj1 (p_env.updatedFuncProp L x (envBox o) x) (eq_refl _)).
    split.
    simpl in H0.
    rewrite _1_b in H2.
    inversion H2.
    rewrite H5 in *.
    set (lem := (proj1 (p_gamma.updatedFuncProp gamma x (typt_box c) x) (eq_refl _))).
    simpl in lem.
    rewrite lem in H0.
    inversion H0.
    f_equal.
    exact H4.
    
    (* 4 *)
    intro.
    rename x0 into z.
    rename sigma1 into tau.
    rename sigma0 into sigma'.
    assert (p_gamma.func Gamma z = Some tau) as _4_a.
    rewrite <- H0.
    symmetry.
    apply p_gamma.updatedFuncProp. firstorder.

    destruct X1 as [ _4_c_i _4_c_ii].
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
    intros envVar' _4_ca_ii.

    assert (p_env.func (p_env.updatePartFunc L x envVar ) z = Some envVar') as _4_cb.
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
  Qed.


  Theorem preservation_case_null :
    forall H L t sigma ann x ,
      WF_Frame' H (ann_frame (sframe L t_let x <- Null t_in (t)) ann) sigma ->
      WF_Frame' H (ann_frame (sframe (p_env.updatePartFunc L x envNull) t ) ann) sigma.
    intros.
    rename X into asm1.
    
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
    
    apply (t_frame1' H (p_gamma.updatePartFunc Gamma x sigma' )
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
    (* assert (p_gamma.func (p_gamma.updatePartFunc Gamma x sigma') x = Some sigma') as _10_a. *)

    (* exact (proj1 (p_gamma.updatedFuncProp Gamma  x sigma' x) (eq_refl x)). *)
    (* rewrite -> _10_a in _8; inversion _8. rewrite <- H1 in *; clear H1 tau _8. *)
    (* unfold WF_Var. *)
    apply inl.
    apply inl.
    exact (proj1 (p_env.updatedFuncProp L  x  envNull x) (eq_refl x)).

    intro x_neq_z. 
    assert (p_gamma.func Gamma z = Some tau) as new_4_a.
    rewrite <- _8.
    symmetry.
    apply (proj2 (p_gamma.updatedFuncProp Gamma x sigma' z)).
    firstorder.
    
    (* set (new__4_d := _6_b z tau _4_a). *)
    unfold WF_Var.
    
    (* rewrite H0. *)
    
    
    
    (* Require Import Coq.Lists.List. *)
    assert (In z (p_gamma.domain Gamma)) as new_4_ca.
    set (lem := p_gamma.fDomainCompat Gamma z).
    set (in_or_not := in_dec v_eq_dec z (p_gamma.domain Gamma)).
    firstorder. rewrite H0 in new_4_a; discriminate.

    set (lem''' := _6_a z new_4_ca).
    case_eq (p_env.func L z).
    intros envVar new__4_ca_ii.

    assert (p_env.func (p_env.updatePartFunc L x envNull ) z = Some envVar) as new_4_cb.
    transitivity (p_env.func L z).
    apply p_env.updatedFuncProp. firstorder.
    exact new__4_ca_ii.
    set (new_4d := _6_b z tau new_4_a).
    unfold WF_Var in new_4d.
    rewrite new_4_cb in *.
    rewrite new__4_ca_ii in *.
    rewrite new_4_a in *.
    rewrite _8.
    exact new_4d.

    intro.
    set (lem'''':= proj2 (p_env.fDomainCompat L z ) H0).
    firstorder.
  Qed.

  Theorem preservation_case_new :
    forall H L sigma ann t C x o flds,
      WF_Frame' H (ann_frame (sframe L t_let x <- New C t_in (t)) ann) sigma ->
      Heap_okP H ->
      ~ In o (p_heap.domain H) ->
      isTerm t ->
      fieldsP C flds ->
      WF_Frame'
        (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))
        (ann_frame (sframe (p_env.updatePartFunc L x (envRef o)) t) ann) sigma.
    intros.
    rename X into asm2.
    rename H2 into H5.
    rename H0 into asm3.
    rename H3 into H11.
    rename H1 into H10.
    

    (* 2 *)
    inversion asm2.
    rename X into _2_a.
    rename X0 into _2_b.
    clear H3 sigma0.
    clear H6 ann0.
    clear t0 H4 L0 H1 H0 H2.

    (* 3 *)
    inversion _2_b.
    rename H0 into _3_a.
    rename X into _3_b.

    (* 4 *)
    inversion _2_a.
    clear tau H2 t0 H6 x0 H3 eff0 H1 gamma H0.
    rename sigma0 into sigma'.
    rename X0 into _4_b.
    rename X into _4_a.
    clear H4 e.


    (* 5 *)
    inversion _4_a.
    clear H3 C0 eff0 H1 H0 gamma.
    rewrite <- H2 in *; clear H2.

    (* section between 5, 6 let's call it half_6 *)
    (* This is not in the same order on paper *)
    (* split. *)
    apply ( t_frame1' _
                     (p_gamma.updatePartFunc Gamma x (typt_class C))
                     eff _ _ ann sigma).
    exact H5.
    exact _4_b.
    assert (gamma_env_subset (p_gamma.updatePartFunc Gamma x (typt_class C))
     (p_env.updatePartFunc L x (envRef o))) as _7.
    exact (subset_preserved Gamma L x sigma' envNull _3_a). (* actually, 7 *)
    split. exact _7.
    intros z tau.
    case_eq (v_eq_dec x z).
    intro x_is_z; rewrite <- x_is_z in *; clear x_is_z z.
    intro dummy; clear dummy.
    (* Section half 6 on paper here somewhere *)
    intro half_6.
    set (half_6_a_i := proj1 (p_env.updatedFuncProp L x (envRef o) x) (eq_refl _)).
    assert (In o (p_heap.domain (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))))
      as o_witn.
    apply p_heap.updatedFuncIn.
    set (H'o := proj1 (p_heap.updatedFuncProp H o (obj C (p_FM.newPartFunc flds FM_null)) o)
                      (eq_refl _)).
    assert ((heap_typeof
               (p_heap.updatePartFunc H o
                                      (obj C (p_FM.newPartFunc flds FM_null)))
               o o_witn) = C) as half_6_a_ii_first.
    unfold heap_typeof.
    rewrite H'o.
    reflexivity.

    
    assert (subtypeP ( typt_class (heap_typeof
                                     (p_heap.updatePartFunc H o
                                                            (obj C (p_FM.newPartFunc flds FM_null)))
                                     o o_witn)) (typt_class C)) as half_6_a_ii.
    rewrite half_6_a_ii_first.
    unfold subtypeP.
    apply classSub.
    apply subclass_refl. (* admitted (actually not defined) *)
    set (lem := proj1 (p_gamma.updatedFuncProp Gamma x (typt_class C) x) (eq_refl _)).
    rewrite half_6 in lem.
    inversion lem.
    rewrite H1 in *; clear lem H1 tau.
    rename half_6 into half_6_a_iii.
    apply inl. apply inr. exists (C, o).
    exists o_witn.
    split.
    exact half_6_a_i.
    split.
    exact half_6_a_iii.
    exact half_6_a_ii.

    (* 6 [THIS starts like #4 from E-Null]*)
    
    intros _6_c dummy _6_a.
    clear dummy.
    
        
    assert (p_gamma.func Gamma z = Some tau) as e_vi.
    rewrite <- _6_a.
    symmetry.
    apply (proj2 (p_gamma.updatedFuncProp Gamma x (typt_class C) z)).
    firstorder.
    
    (* set (new__4_d := _6_b z tau _4_a). *)
    (* unfold WF_Var. *)
    
    (* rewrite H0. *)
    

    
    (* Require Import Coq.Lists.List. *)
    assert (In z (p_gamma.domain Gamma)) as z_in_dom_Gamma.
    set (lem := p_gamma.fDomainCompat Gamma z).
    set (in_or_not := in_dec v_eq_dec z (p_gamma.domain Gamma)).
    firstorder. rewrite H0 in e_vi; discriminate.

    

    set (z_in_dom_L := _3_a z z_in_dom_Gamma).
    case_eq (p_env.func L z).
    intros envVar L_z_val.
    assert (p_env.func (p_env.updatePartFunc L x (envRef o) ) z = Some envVar) as _6_bb.
    transitivity (p_env.func L z).
    apply p_env.updatedFuncProp. firstorder.
    exact L_z_val.

    destruct envVar.

    (* 6 d *)
    apply inl. apply inl.
    exact _6_bb.

    (* 6 e *)

    rename r into o'.

    assert ({ C | {witn |
             p_env.func L z = Some (envRef o') /\
             p_gamma.func Gamma z = Some (typt_class C) /\
             subtypeP (typt_class (heap_typeof H o' witn)) (typt_class C)
            }}).
    elim (_3_b z tau e_vi).
    intro.
    destruct a.
    rewrite -> e in L_z_val; discriminate.
    destruct s.
    destruct x0.
    destruct y.
    destruct a.
    destruct H1.
    rewrite L_z_val in H0.
    inversion H0.
    rewrite H4 in *; clear H4 o'; rename r into o'.
    clear H0.
    rewrite e_vi in H1.
    inversion H1. rewrite -> H3 in *.
    clear H3 tau H1.
    exists c. exists x0.
    split.
    exact L_z_val.
    split.
    exact e_vi.
    exact H2.

    intro.
    destruct b. destruct x0. destruct y. destruct a. destruct H1.
    exists c.
    rewrite L_z_val in H0.
    inversion H0.
    destruct X. destruct s. destruct a. destruct H1.
    clear H0.
    rename x0 into C'.
    rename x1 into o'_witness.

    apply inl. apply inr.
    exists (C', o').
    exists (p_heap.staysInDomain H o (obj C (p_FM.newPartFunc flds FM_null)) o' o'_witness).
    split.
    exact _6_bb.
    split.
    rewrite <- H1.
    apply (p_gamma.updatedFuncProp). firstorder.
    admit. 
    admit.
    admit.
    Admitted.

    
  (*   P : Program *)
  (* H : Heap_type *)
  (* L : Env_type *)
  (* sigma : typecheck_type *)
  (* ann : annotation_type *)
  (* t : ExprOrTerm *)
  (* C : ClassName_type *)
  (* x : VarName_type *)
  (* asm2 : WF_Frame' H (ann_frame (sframe L t_let x <- New C t_in (t)) ann) *)
  (*          sigma *)
  (* asm3 : Heap_okP H *)
  (* o : p_gamma.A *)
  (* FM : p_FM.PartFunc *)
  (* flds : list FieldName_type *)
  (* asm1 : Reduction_SF' ( # H, L, t_let x <- New C t_in (t) ! ) *)
  (*          ( # p_heap.updatePartFunc H o *)
  (*                (obj C (p_FM.newPartFunc flds FM_null)), *)
  (*          p_env.updatePartFunc L x (envRef o), t ! ) *)
  (* H5 : isTerm t *)
  (* H10 : ~ In o (p_heap.domain H) *)
  (* H11 : fields reductions.P C flds *)
  (* ============================ *)
  (*  WF_Frame' *)
  (*    (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null))) *)
  (*    (ann_frame (sframe (p_env.updatePartFunc L x (envRef o)) t) ann) sigma * *)
  (*  Heap_okP *)
  (*    (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null))) *)

  Theorem preservation_case_box :
    forall H L sigma ann t C x o flds,
      WF_Frame' H (ann_frame (sframe L t_let x <- Box C t_in (t)) ann) sigma ->
      Heap_okP H ->
      ~ In o (p_heap.domain H) ->
      isTerm t ->
      fieldsP C flds ->
      WF_Frame'
        (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))
        (ann_frame (sframe (p_env.updatePartFunc L x (envBox o)) t) ann) sigma.
    admit. Admitted.

  Theorem preservation_case_select :
    forall H L sigma ann x y f t C FM fmVal o,
      WF_Frame' H (ann_frame (sframe L t_let x <- FieldSelection y f t_in (t)) ann) sigma ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_FM.func FM f = Some fmVal ->
      isTerm t ->
      WF_Frame'
        H
        (ann_frame (sframe (p_env.updatePartFunc L x (fm2env fmVal)) t) ann) sigma.
    intros.

    (* 2 *)
    rename H1 into _2_ab.
    rename H2 into _2_cd.
    rename H3 into _2_e.
    rename H4 into t_is_term.
    rename H0 into _2_j.
    rename X into _2_k.

    (* 3 *)
    inversion _2_k.
    clear H3 sigma0 H5 ann0 H4 H1 H2.
    rename X into _3_a.
    rename X0 into _3_b.


    (* 4 *)
    inversion _3_a.
    clear tau H3 H7 t1 H5 e H4 x0 eff0 H2.
    rewrite <- H1 in * ; clear H1 Gamma.
    inversion X.
    clear H5 f0 H1 x0 eff0 H3 gamma0 H2.
    rename C0 into D.
    rename H7 into _4_a.
    rename witn into _4_b.
    set (E := ftype P D f _4_b).
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
    inversion _3_b.
    rename H0 into _3_b_i.
    rename X into _3_b_ii.
    set (_6 := subset_preserved gamma L x (typt_class E) (fm2env fmVal)  _3_b_i).


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
    assert (p_env.func L' x = Some (fm2env fmVal)) as _7_a.
    unfold L'.
    rewrite  ( proj1 (p_env.updatedFuncProp L x (fm2env fmVal) x) (eq_refl x)).
    reflexivity.
    
    assert (p_gamma.func Gamma' x = Some (typt_class E)) as gamma_x_E.
    unfold Gamma'.
    rewrite  ( proj1 (p_gamma.updatedFuncProp gamma x (typt_class E) x) (eq_refl x)).
    reflexivity.
    clear H1.

    (* 7 b *)
    induction fmVal; unfold fm2env in _7_a.
    
    (* 7 b i *)
    apply inl. apply inl.
    exact _7_a.

    (* 7 c *)
    rename r into o'.
    set (test := _2_j o C FM _2_cd f o').
    
    Print Heap_obj_ok.
    apply inl.  apply inr.
    exists (E, o').
    Print p_heap.fDomainCompat.
    unfold Gamma'.
    assert (subclass P C D) as C_sub_D.
    
    induction ( _3_b_ii y (typt_class D) _4_a).
    induction a.
    rewrite  _2_ab in a; discriminate a.
    destruct b.
    destruct x0.
    destruct y0.
    destruct a.
    destruct H1.
    rewrite _2_ab in H0.
    inversion H0.
    rewrite H4 in *.
    rewrite _4_a in H1.
    inversion H1.
    rewrite <- H5 in *.
    clear c H5.
    assert (heap_typeof H r x0 = C).
    unfold heap_typeof.
    rewrite <- H4.
    rewrite _2_cd.
    reflexivity.
    rewrite H3 in H2.
    inversion H2.
    exact H7.
    destruct b.   destruct x0. 
    destruct y0.
    destruct a.
    rewrite _2_ab in H0.
    inversion H0.
    
    assert (fld P C f) as f_field_C.
    apply (field_subclass P C D  _  _4_b).
    
    exact C_sub_D.
    destruct (test f_field_C _2_e).
    clear test.
    exists x0.
    split.
    exact _7_a.
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
    apply (_3_b_i _ _8_a).

    set (_8_e_i := _3_b_ii z tau _8_b).
    unfold WF_Var.

    assert (p_env.func L z = p_env.func L' z) as _8_d.
    set (lem := proj2 (p_env.updatedFuncProp L x (fm2env fmVal) z)).
    symmetry. firstorder.
    rewrite <- _8_d.
    rewrite <- _8_b in H1.
    rewrite H1.
    exact _8_e_i.
  Qed.


  Theorem single_frame_WF_ENV_preservation :
    forall H H' L L' t t' sigma ann,
      WF_Frame' H (ann_frame (sframe L t) ann) sigma ->
      Heap_okP H ->
      Reduction_SF' ( # H, L, t !) ( # H', L', t' !) ->
      (WF_Frame' H' (ann_frame (sframe L' t') ann) sigma) *
      (Heap_okP H').
    intros.
    rename H0 into asm0.
    case_eq t; intros;   rewrite H0 in *  ;    clear H0 t;   inversion X0.

    (* Case let x = y in t *)
    
    rewrite <- H7 in *; clear H7 H1 H0.
    rewrite <- H8 in *; clear H2 L0 H8.
    rewrite <- H6 in *; rewrite <- H9 in *; clear  H9 H6.
    rewrite <- H5 in *; clear H5.
    rewrite <- H4 in *; clear H4.
    Check preservation_case_var.

    split.
    exact (preservation_case_var H L x y t sigma ann null_ref_box X H10 H3).
    assumption.
    
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
    rename asm0 into asm2.
    rename X0 into asm0.
    clear H2 . 

    clear v.

    split.

    exact (preservation_case_null H L t sigma ann x asm1).
    exact asm2.


    (* Case let v = new C in t *)

    

    
    
    rename X0 into asm1.
    rename X into asm2.
    rename asm0 into asm3.

    (* 1 *)

    rewrite -> H9 in *; clear H9 e0.
    rewrite <- H6 in *; clear H6 t'.
    rewrite <- H8  in *; clear L' H8.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H4 in *; clear e H4.
    rewrite <- H3 in *; clear H3 v.
    clear H2 L0 H0 H1.
    rewrite H12 in *; clear H12.

    split.
    Check preservation_case_new.
    exact (preservation_case_new H L sigma ann t C x o flds asm2 asm3 H10 H5 H11).


    (* intros. *)
    (* exact i. *)
    (* intros not_in dummy; clear dummy. *)
    (* set (H'o'_is_none := proj1 ((p_heap.fDomainCompat  *)
    (*                 (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null))) *)
    (*                             ) o' ) not_in). *)

    
    
           
    (* set (new_4d := _3_b z tau new_4_a). *)
    (* unfold WF_Var in new_4d. *)
    (* rewrite new_4_cb in *. *)
    (* rewrite new__4_ca_ii in *. *)
    (* rewrite new_4_a in *. *)
    (* rewrite _6. *)

    (* (* 6 a *) *)
    (* induction envVar. *)
    
    (* apply inl. apply inl. reflexivity. *)
    (* case_eq (rn_eq_dec r o). *)
    (* intros r_o_eq dummy'. clear dummy' dummy. *)
    (* rewrite r_o_eq in *. *)
    
    (* set (lemm := proj1 (p_heap.updatedFuncProp H o (obj C (p_FM.newPartFunc flds FM_null)) o) *)
    (*                      (eq_refl _) *)
    (*         ). *)
    
    (* destruct new_4d. *)
    (* destruct s. *)
    (* inversion e. *)
    (* destruct s. *)
    (* destruct x0. *)
    (* destruct y. *)
    (* destruct a. *)
    (* inversion H0. *)
    (* rewrite -> H3 in *. *)
    (* clear o H3. *)
    (* rename r0 into o. *)
    (* clear r_o_eq r. *)
    (* clear H0. *)
    (* destruct H1. *)
    (* inversion H0. *)
    (* rewrite -> H3 in *. *)
    (* clear H3 tau. *)
    (* clear H0. *)
    
    
    (* destruct s. *)
    (* apply inl. apply inl. *)
    (* exact e. *)
    (* apply inl. apply inr. *)
    (* destruct s. *)
    (* destruct x0. *)
    (* exists (c, r). *)
    (* destruct y. *)
    (* TODO FINISH!!! *)
    (* intro. *)
    (* set (lem'''':= proj2 (p_env.fDomainCompat L z ) H0). *)
    (* firstorder. *)
    
    
        
    (* (* Section half_6 from paper: *) *)
    
    (* assert (p_env.updatePartFunc L x (envRef o) ) *)
    
    
    (*                  Gamma eff t L ann sigma,) *)
    
    (* set (_2_A := t) *)
    admit.
    
    
    
    (* Case let x = Box C in t*)
    Check    preservation_case_box.
    split.
    rewrite <- H6 in *; clear H6.
    rewrite <- H9 in *; clear H9 t' e0.
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H4 in *; clear e H4.
    rewrite <- H3 in *; clear H3 v.
    clear H2 L0 H1 H0.
    rewrite H12 in *; clear H12 FM.
    apply (preservation_case_box H L sigma ann t C x o flds X asm0 H10 H5 H11).
    admit.



    (* Case SELECT, let x = y.f in t *)
    split.

    rewrite <- H6 in *; clear H6 e0.
    rewrite <- H9 in *; clear H9 t'.
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H4 in *; clear H4 e.
    rewrite <- H3 in *; clear H3 v.
    clear L0 H0 H2 H1.
    Check preservation_case_select.
    apply (preservation_case_select H L sigma ann x y f t C FM fmVal o X asm0 H10 H11 H12 H5).
    rewrite <- H7; exact asm0.

    (* Case ASSIGN, let x = (y.f = z) in t *)
    admit.
    Admitted.


  
    