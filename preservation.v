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

  Definition Reduction_SF' := Reduction_SF P .
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecks P.
  Definition Heap_okP := Heap_ok P.
  Definition Heap_dom_okP := Heap_dom_ok P .
  
  
  
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
    exists (p_gamma.updatePartFunc gamma v sigma0); auto;
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
    rewrite <- H2 in *; rewrite <- H4 in *.
    clear H1 H0 C0 H2 H4 H2 eff.
    rename H3 into C_is_ocap.


    (* section between 5, 6 let's call it half_6 *)
    (* This is not in the same order on paper *)
    (* split. *)
    apply ( t_frame1' _
                     (p_gamma.updatePartFunc Gamma x (typt_class C))
                     eff_ocap _ _ ann sigma).
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
    apply (heap_typeof_same P _ _ _ _ H'o).
    
    (* rewrite e. *)
    (* reflexivity. *)

    
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

    set (H' := (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))).
    apply classSub.
    inversion H2.
    assert (p_heap.func H o' = p_heap.func H' o') as _6_e_ii.
    apply (p_heap.freshProp _ _ _ H10 _ o'_witness).
    assert ((heap_typeof H' o'
                         (p_heap.staysInDomain H o (obj C (p_FM.newPartFunc flds FM_null)) o'
                                               o'_witness))
            = (heap_typeof H o' o'_witness))
      as _6_e_iii.

    case_eq (p_heap.func H o').
    intros. destruct b.
    set (stays_witn := (p_heap.staysInDomain
                          H o
                          (obj C
                               (p_FM.newPartFunc flds FM_null)) o'
                          o'_witness)).
    fold stays_witn.
    rewrite <- H0 in *.
    rewrite _6_e_ii in H6.
    assert (c = C0).
    symmetry in H0.
    set (lem := heap_typeof_impl P _ _ _ _ H0).
    destruct lem.
    rewrite H6 in _6_e_ii.
    rewrite e in _6_e_ii.
    inversion _6_e_ii.
    reflexivity.
    rewrite <- H8.
    apply (heap_typeof_same P _ _ _ _ H6).

    (* None *)
    intro is_none;  induction (proj2 (p_heap.fDomainCompat _ _)
                                     is_none o'_witness).
        
    rewrite _6_e_iii.
    exact H4.
    
    (* 6 L(z) = box o' *)
    rename r into o'.
    set (H' := (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))).
    set (Gamma' := (p_gamma.updatePartFunc Gamma x (typt_class C))).
    fold Gamma' in _4_b, _7, _6_a.
    set (L' := (p_env.updatePartFunc L x (envRef o))).
    fold L' in _7, _6_bb.

    set (o_is_WF := _3_b z tau e_vi).
    inversion o_is_WF.
    destruct X.
    rewrite e in L_z_val.
    inversion L_z_val.
    destruct s.
    destruct x0.
    destruct y.
    destruct a.
    rewrite H0 in L_z_val.
    inversion L_z_val.

    destruct X.  destruct x0.    destruct y. destruct a. destruct H1.
    rewrite H0 in L_z_val.
    inversion L_z_val.
    rewrite <- H4 in *.
    clear o' H4.
    rename r into o'.
    clear L_z_val.
    apply inr.
    exists (c, o').
    exists (p_heap.staysInDomain _ _ _ _ x0).
    split.
    rewrite <- H0.
    apply (proj2 (p_env.updatedFuncProp _ _  _ _ )).
    firstorder.
    split.
    rewrite <- H1.
    apply (proj2 (p_gamma.updatedFuncProp _ _  _ _ )).
    firstorder.
    apply classSub.
    inversion H2.
    clear H4 C0 H3.
    assert (p_heap.func H o' = p_heap.func H' o').
    apply (p_heap.freshProp).
    exact H10.
    exact x0.

    set (C' :=  heap_typeof H o' x0).
    fold C' in H6, H2.
    set (stays_witn := (p_heap.staysInDomain
                          H o (obj C (p_FM.newPartFunc flds FM_null)) o'
                          x0)).
    assert ((heap_typeof H' o' stays_witn) = C').

    destruct (heap_typeof_impl P _ _ C' x0 (eq_refl _)).
    rewrite e in H3.
    symmetry in H3.
    apply (heap_typeof_same P _ _ _ _ H3 stays_witn).
    rewrite H4.
    assumption.
    intro L_z_is_none; induction (proj2 (p_env.fDomainCompat _ _) L_z_is_none).
    auto.


    (*** effect EPSILON ***)
    rewrite <- H2 in *;
    rewrite <- H1 in *.
    clear H1 H0 C0 H2 H2 eff H3.
    

    (* section between 5, 6 let's call it half_6 *)
    (* This is not in the same order on paper *)
    (* split. *)
    apply ( t_frame1' _
                     (p_gamma.updatePartFunc Gamma x (typt_class C))
                     eff_epsilon _ _ ann sigma).
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
    apply (heap_typeof_same P _ _ _ _ H'o).
    
    (* rewrite e. *)
    (* reflexivity. *)

    
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

    set (H' := (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))).
    apply classSub.
    inversion H2.
    assert (p_heap.func H o' = p_heap.func H' o') as _6_e_ii.
    apply (p_heap.freshProp _ _ _ H10 _ o'_witness).
    assert ((heap_typeof H' o'
                         (p_heap.staysInDomain H o (obj C (p_FM.newPartFunc flds FM_null)) o'
                                               o'_witness))
            = (heap_typeof H o' o'_witness))
      as _6_e_iii.

    case_eq (p_heap.func H o').
    intros. destruct b.
    set (stays_witn := (p_heap.staysInDomain
                          H o
                          (obj C
                               (p_FM.newPartFunc flds FM_null)) o'
                          o'_witness)).
    fold stays_witn.
    rewrite <- H0 in *.
    rewrite _6_e_ii in H6.
    assert (c = C0).
    symmetry in H0.
    set (lem := heap_typeof_impl P _ _ _ _ H0).
    destruct lem.
    rewrite H6 in _6_e_ii.
    rewrite e in _6_e_ii.
    inversion _6_e_ii.
    reflexivity.
    rewrite <- H8.
    apply (heap_typeof_same P _ _ _ _ H6).

    (* None *)
    intro is_none;  induction (proj2 (p_heap.fDomainCompat _ _)
                                     is_none o'_witness).
        
    rewrite _6_e_iii.
    exact H4.
    
    (* 6 L(z) = box o' *)
    rename r into o'.
    set (H' := (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))).
    set (Gamma' := (p_gamma.updatePartFunc Gamma x (typt_class C))).
    fold Gamma' in _4_b, _7, _6_a.
    set (L' := (p_env.updatePartFunc L x (envRef o))).
    fold L' in _7, _6_bb.

    set (o_is_WF := _3_b z tau e_vi).
    inversion o_is_WF.
    destruct X.
    rewrite e in L_z_val.
    inversion L_z_val.
    destruct s.
    destruct x0.
    destruct y.
    destruct a.
    rewrite H0 in L_z_val.
    inversion L_z_val.

    destruct X.  destruct x0.    destruct y. destruct a. destruct H1.
    rewrite H0 in L_z_val.
    inversion L_z_val.
    rewrite <- H4 in *.
    clear o' H4.
    rename r into o'.
    clear L_z_val.
    apply inr.
    exists (c, o').
    exists (p_heap.staysInDomain _ _ _ _ x0).
    split.
    rewrite <- H0.
    apply (proj2 (p_env.updatedFuncProp _ _  _ _ )).
    firstorder.
    split.
    rewrite <- H1.
    apply (proj2 (p_gamma.updatedFuncProp _ _  _ _ )).
    firstorder.
    apply classSub.
    inversion H2.
    clear H4 C0 H3.
    assert (p_heap.func H o' = p_heap.func H' o').
    apply (p_heap.freshProp).
    exact H10.
    exact x0.
    
    (* TODO: find out why it doesn't work! *)
    set (C' :=  heap_typeof H o' x0).
    fold C' in H6, H2.
    set (stays_witn := (p_heap.staysInDomain
                          H o (obj C (p_FM.newPartFunc flds FM_null)) o'
                          x0)).
    assert ((heap_typeof H' o' stays_witn) = C').

    destruct (heap_typeof_impl P _ _ C' x0 (eq_refl _)).
    rewrite e in H3.
    symmetry in H3.
    apply (heap_typeof_same P _ _ _ _ H3 stays_witn).
    rewrite H4.
    assumption.

    intro L_z_is_none; induction (proj2 (p_env.fDomainCompat _ _) L_z_is_none).
    auto.
  Qed.




  Lemma product_forall AA (PP: AA -> Type) (QQ: AA -> Type):
    (forall a : AA,
       PP a * QQ a) ->
    (forall a, PP a) * (forall a, QQ a).
    firstorder.
  Qed.

  
  Theorem preservation_case_new_heap :
    forall H L sigma ann t C x (o: p_heap.A) flds,
      forall (heap_dom_ok: Heap_dom_okP H),
        WF_Frame' H (ann_frame (sframe L t_let x <- New C t_in (t)) ann) sigma ->
        Heap_okP H ->
        ~ In o (p_heap.domain H) ->
        isTerm t ->
        fieldsP C flds ->
        let H' := (p_heap.updatePartFunc
                     H o (obj C (p_FM.newPartFunc flds FM_null)))
        in 
        (Heap_okP H') *
        (Heap_dom_okP H').
    intros.
    unfold Heap_okP; unfold Heap_ok; unfold Heap_dom_okP;
    unfold Heap_dom_ok.

    
    
    apply product_forall; intro o';
    apply product_forall; intro C0;
    apply product_forall; intro FM.
    apply product_forall; intro H'a_is_obj.

    set (obj' := (obj C (p_FM.newPartFunc flds FM_null)));
    fold obj' in H'.

    case_eq (rn_eq_dec o o'); intros are_eq _.
    rewrite <- are_eq in *; clear o' are_eq.
    set (lem := proj1 (p_heap.updatedFuncProp
                         H o obj' o)
                      (eq_refl _)
        ).
    fold H' in lem.
    rewrite lem in H'a_is_obj; inversion H'a_is_obj.
    rewrite <- H5 in *.
    rewrite <- H6 in *.
    clear H6 H5 H'a_is_obj lem C0 FM. 

    rewrite (p_FM.newPartFuncDomain flds FM_null).
    unfold heap.fieldsP.
    unfold fieldsP in H3.

    split.
    intros f o'' f_is_fld_C FM_o''_is_some.
    set (lem := proj1 (p_FM.newPartFuncProp flds FM_null f) ).
    set (FM := (p_FM.newPartFunc flds FM_null)).
    fold FM in FM_o''_is_some, lem.
    assert (In f flds) as f_in_flds.
    
    set (lem'' := p_FM.fDomainCompat FM f).

    case_eq (in_dec fn_eq_dec f flds).
    intros is_in _; assumption.
    intros not_in _.
    firstorder.
    rewrite H4 in FM_o''_is_some.
    discriminate.

    set (lem'' := proj1 lem f_in_flds).
    rewrite lem'' in FM_o''_is_some; discriminate.
    assumption.

    assert (o' <> o). firstorder.

    set (lem := proj2 (p_heap.updatedFuncProp
                         H o obj' o')
                      H4
        ).
    clear are_eq.
    fold H' in lem.


    destruct X.
    clear Gamma eff t0 L0 ann0 sigma i t1 w H2.
    rewrite lem in H'a_is_obj.
    split.
    unfold Heap_obj_ok.
    intros f o'' f_witn FM_f_eq.
    destruct (H0 _ _ _ H'a_is_obj f o'' f_witn FM_f_eq) as
        [o''_in_H C''_sub_ftype].
    set (C'' := (heap_typeof H o'' o''_in_H)).
    fold C'' in C''_sub_ftype.
    exists (p_heap.staysInDomain _ _ _ _  o''_in_H).
    set (o''_in_H' := (p_heap.staysInDomain H o obj' o'' o''_in_H)).
    assert ((heap_typeof H' o'' o''_in_H') = C'').

    set (lemlem := p_heap.freshProp _ _ obj' H1 _ o''_in_H).
    fold H' in lemlem.
    clear lem H'a_is_obj f_witn C0 C''_sub_ftype FM FM_f_eq o' H4 f.

    destruct (heap_typeof_impl P H o'' C'' o''_in_H (eq_refl _))
      as [FM'' Ho''].
    rewrite Ho'' in lemlem; symmetry in lemlem.
    apply (heap_typeof_same P _ _ _ FM''); assumption.
    rewrite H2; assumption.
    unfold heap.fieldsP.
    clear H' lem H4 obj' H1 H3.
    exact (heap_dom_ok o' C0 FM H'a_is_obj).
  Qed.


  Theorem preservation_case_box_heap :
    forall H L sigma ann t C x (o: p_heap.A) flds,
      forall (heap_dom_ok: Heap_dom_okP H),
        WF_Frame' H (ann_frame (sframe L t_let x <- Box C t_in (t)) ann) sigma ->
        Heap_okP H ->
        ~ In o (p_heap.domain H) ->
        isTerm t ->
        fieldsP C flds ->
        let H' := (p_heap.updatePartFunc
                     H o (obj C (p_FM.newPartFunc flds FM_null)))
        in 
        (Heap_okP H') *
        (Heap_dom_okP H').
    intros.
    unfold Heap_okP; unfold Heap_ok; unfold Heap_dom_okP;
    unfold Heap_dom_ok.

    
    
    apply product_forall; intro o';
    apply product_forall; intro C0;
    apply product_forall; intro FM.
    apply product_forall; intro H'a_is_obj.

    set (obj' := (obj C (p_FM.newPartFunc flds FM_null)));
    fold obj' in H'.

    case_eq (rn_eq_dec o o'); intros are_eq _.
    rewrite <- are_eq in *; clear o' are_eq.
    set (lem := proj1 (p_heap.updatedFuncProp
                         H o obj' o)
                      (eq_refl _)
        ).
    fold H' in lem.
    rewrite lem in H'a_is_obj; inversion H'a_is_obj.
    rewrite <- H5 in *.
    rewrite <- H6 in *.
    clear H6 H5 H'a_is_obj lem C0 FM. 

    rewrite (p_FM.newPartFuncDomain flds FM_null).
    unfold heap.fieldsP.
    unfold fieldsP in H3.

    split.
    intros f o'' f_is_fld_C FM_o''_is_some.
    set (lem := proj1 (p_FM.newPartFuncProp flds FM_null f) ).
    set (FM := (p_FM.newPartFunc flds FM_null)).
    fold FM in FM_o''_is_some, lem.
    assert (In f flds) as f_in_flds.
    
    set (lem'' := p_FM.fDomainCompat FM f).

    case_eq (in_dec fn_eq_dec f flds).
    intros is_in _; assumption.
    intros not_in _.
    firstorder.
    rewrite H4 in FM_o''_is_some.
    discriminate.

    set (lem'' := proj1 lem f_in_flds).
    rewrite lem'' in FM_o''_is_some; discriminate.
    assumption.

    assert (o' <> o). firstorder.

    set (lem := proj2 (p_heap.updatedFuncProp
                         H o obj' o')
                      H4
        ).
    clear are_eq.
    fold H' in lem.


    destruct X.
    clear Gamma eff t0 L0 ann0 sigma i t1 w H2.
    rewrite lem in H'a_is_obj.
    split.
    unfold Heap_obj_ok.
    intros f o'' f_witn FM_f_eq.
    destruct (H0 _ _ _ H'a_is_obj f o'' f_witn FM_f_eq) as
        [o''_in_H C''_sub_ftype].
    set (C'' := (heap_typeof H o'' o''_in_H)).
    fold C'' in C''_sub_ftype.
    exists (p_heap.staysInDomain _ _ _ _  o''_in_H).
    set (o''_in_H' := (p_heap.staysInDomain H o obj' o'' o''_in_H)).
    assert ((heap_typeof H' o'' o''_in_H') = C'').

    set (lemlem := p_heap.freshProp _ _ obj' H1 _ o''_in_H).
    fold H' in lemlem.
    clear lem H'a_is_obj f_witn C0 C''_sub_ftype FM FM_f_eq o' H4 f.

    destruct (heap_typeof_impl P H o'' C'' o''_in_H (eq_refl _))
      as [FM'' Ho''].
    rewrite Ho'' in lemlem; symmetry in lemlem.
    apply (heap_typeof_same P _ _ _ FM''); assumption.
    rewrite H2; assumption.
    unfold heap.fieldsP.
    clear H' lem H4 obj' H1 H3.
    exact (heap_dom_ok o' C0 FM H'a_is_obj).
  Qed.
  
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
    
    apply inl.  apply inr.
    exists (E, o').
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
  Admitted.




  Theorem preservation_case_assign H L x y f z t C FM o sigma envVal ann:
    forall witn: is_not_box envVal,
      WF_Frame' H (ann_frame (sframe L t_let x <- (FieldAssignment y f z) t_in (t)) ann) sigma ->
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
    assert ({o_z | envVal = envRef o_z} + (envVal = envNull)) as _2_b.
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
    rename X into _3_a.
    rename X0 into _3_b.

    (* 4 *)
    inversion _3_a.
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
    set (_4_a := p_gamma.in_part_func_domain Gamma y (typt_class C1) H4).
    set (_4_b := p_gamma.in_part_func_domain Gamma z (typt_class C0) H14).
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
    inversion _3_b.
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
    case_eq _2_b.
    intros.
    clear H0 _2_b.
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
    case_eq (v_eq_dec o_z o_y).
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
    intros _7 dummy tau _7';    clear dummy.
    assert (p_gamma.func Gamma' s = p_gamma.func Gamma s) as _7_a.
    apply (proj2 (p_gamma.updatedFuncProp _ _ _ _) _7).
    assert (p_env.func L' s = p_env.func L s) as _7_b.
    apply (proj2 (p_env.updatedFuncProp _ _ _ _) _7).
    rewrite _7' in _7_a.
    symmetry in _7_a.
    set (_7_c := _5_b s tau _7_a).

    case_eq (p_env.func L s).
    intros.
    case_eq b.
    intros.
    apply inl. apply inl.
    rewrite H1 in H0.
    rewrite H0 in _7_b.
    assumption.

    (* 7 e, b = envRef o_s *)
    clear _1_c.
    clear ann.
    intros.
    rename r into o_s.
    rewrite H1 in *.
    destruct _7_c. (* case analysis on WF-var Gamma L s *)
    destruct s0.
    rewrite H0 in e; discriminate e.
    destruct s0.
    destruct x0; destruct y0; destruct a; destruct H5.
    rewrite H2 in H0;    inversion H0.
    rewrite <- H9 in *; clear H9.
    clear o_s; rename r into o_s.
    clear H0 b H1.
    rename H5 into _7_e_i.
    rename c into G.
    rename H6 into _7_e_ii.
    set (stays := p_heap.staysInDomain H o_y (obj C' FM') o_s x0).
    fold H' in stays.

    (* 7 e iii *)
    assert (heap_typeof H o_s x0 = heap_typeof H' o_s stays) as _7_e_iii.
    case_eq (v_eq_dec o_s o_y).
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
    
    set (lem := _5_b s tau _7_a).
    unfold WF_Var.
    rewrite _7_b.
    rewrite _7'.

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
    rewrite H1 in _7_a.
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

    case_eq (v_eq_dec o_s o_y).
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
    set (lem := _5_b s tau _7_a).
    destruct lem.
    destruct s0.
    rewrite e in H0; discriminate H0.
    destruct s0; destruct x0; destruct y0; destruct a.
    rewrite H2 in H0; discriminate H0.
    destruct s0; destruct x0; destruct y0; destruct a; destruct H5.
    rewrite H2 in H0; simplify_eq H0.
    intro equRef; rewrite equRef in *.
    clear H0.
    rewrite _7_a in H5; simplify_eq H5.
    intro equTy; rewrite equTy in *.
    rename c into F.
    rename _7' into _7_f_i_A.
    assert (In o_s (p_heap.domain H)).
    rewrite <- equRef.
    assumption.
    assert (In o_s (p_heap.domain H')).
    unfold H'.
    apply (p_heap.staysInDomain H _ _ o_s).
    assumption.
    assert (heap_typeof H o_s H0  = heap_typeof H' o_s H8) as _7_f_ii.

    case_eq (v_eq_dec o_s o_y).
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
    rewrite _7_b.
    rewrite _7_f_i_A.
    rewrite H2.
    apply inr.
    exists (F, o_s).
    exists H8.
    split.
    reflexivity.
    split.
    reflexivity.
    rewrite <- _7_f_ii.
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
    set (s_in_gamma := p_gamma.in_part_func_domain Gamma s tau _7_a).
    set (lem := _5_a _ s_in_gamma).
    elim (proj2 (p_env.fDomainCompat _ _) H0 lem).

    (* HEAP OK *)

    intro.
    rename o into o_y.
    rename o0 into o.

    case_eq (v_eq_dec o_y o).
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

  (* Qed. *)


  Theorem single_frame_WF_ENV_preservation :
    forall H H' L L' t t' sigma ann,
      forall (heap_dom_ok: Heap_dom_okP H),
      WF_Frame' H (ann_frame (sframe L t) ann) sigma ->
      Heap_okP H ->
      Reduction_SF' ( # H, L, t !) ( # H', L', t' !) ->
      ((WF_Frame' H' (ann_frame (sframe L' t') ann) sigma) *
       (Heap_okP H') *
       (Heap_dom_okP H')
      ).
    intros.
    rename H0 into asm0.
    case_eq t; intros;   rewrite H0 in *  ;    clear H0 t;   inversion X0.

    (* Case let x = y in t *)
    
    rewrite <- H7 in *; clear H7 H1 H0.
    rewrite <- H8 in *; clear H2 L0 H8.
    rewrite <- H6 in *; rewrite <- H9 in *; clear  H9 H6.
    rewrite <- H5 in *; clear H5.
    rewrite <- H4 in *; clear H4.
    
    split.
    split.
    
    exact (preservation_case_var H L x y t sigma ann null_ref_box X H10 H3).
    assumption.
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
    split.
    exact (preservation_case_null H L t sigma ann x asm1).
    exact asm2.
    assumption.


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
    split.
       
    exact (preservation_case_new H L sigma ann t C x o flds asm2 asm3 H10 H5 H11).
    set (FM' := (p_FM.newPartFunc flds FM_null)).
    set (obj' :=(obj C FM')).
    set (H' := (p_heap.updatePartFunc H o obj')).
    apply (preservation_case_new_heap H L sigma ann t C x o flds heap_dom_ok
                                      asm2 asm3 H10 H5 H11
          ).
    apply (preservation_case_new_heap H L sigma ann t C x o flds heap_dom_ok
                                      asm2 asm3 H10 H5 H11
          ).

    
    
    (* Case let x = Box C in t*)
    rewrite <- H6 in *; clear H6.
    rewrite <- H9 in *; clear H9 t' e0.
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H4 in *; clear e H4.
    rewrite <- H3 in *; clear H3 v.
    clear H2 L0 H1 H0.
    rewrite H12 in *; clear H12 FM.
    split. split.
    apply (preservation_case_box H L sigma ann t C x o flds X asm0 H10 H5 H11).

    (* TWO ADMITS BELOW: change to the following. *)
    apply (preservation_case_box_heap H L sigma ann t C x o flds heap_dom_ok
                                      X asm0 H10 H5 H11
          ).
    apply (preservation_case_box_heap H L sigma ann t C x o flds heap_dom_ok
                                      X asm0 H10 H5 H11
          ).


    (* Case SELECT, let x = y.f in t *)
    split. split.

    rewrite <- H6 in *; clear H6 e0.
    rewrite <- H9 in *; clear H9 t'.
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H4 in *; clear H4 e.
    rewrite <- H3 in *; clear H3 v.
    clear L0 H0 H2 H1.
    apply (preservation_case_select H L sigma ann x y f t C FM fmVal o X asm0 H10 H11 H12 H5).
    rewrite <- H7; exact asm0.
    admit.

    (* Case ASSIGN, let x = (y.f = z) in t *)

    rewrite <- H5 in *.
    rewrite <- H9 in *.
    clear H9.

    rewrite <- H3 in *.
    clear v H3.
    clear H5 e0.
    rewrite <- H4 in *.
    clear H4 e.
    split.

    exact (preservation_case_assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ X asm0 H10
                                    H11 H13
          ).
    admit.
  Admitted.

  
End Preservation.