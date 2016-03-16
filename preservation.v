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

  Local Open Scope type_scope.

  

  Theorem single_frame_WF_ENV_preservation :
    forall H H' L L' t t' sigma ann,
      WF_Frame' H (ann_frame (sframe L t) ann) sigma ->
      Heap_ok H ->
      Reduction_SF ( # H, L, t !) ( # H', L', t' !) ->
      (WF_Frame' H' (ann_frame (sframe L' t') ann) sigma) *
      (Heap_ok H').
    intros.
    rename H0 into asm0.
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
    split.
    apply (t_frame1' H (p_gamma.updatePartFunc Gamma x sigma0) eff t
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

    destruct b; destruct x2; destruct y0; destruct a; destruct H2.
    (* induction b; destruct x2; induction p; destruct p; destruct H2. *)

    rewrite (_3_b_i_A) in *; inversion H1.
    (* destruct H2. *)
    (* rewrite ->  H8 in *. *)
    (* clear o H8. *)
    (* rename r into o. (* it couldn't do it directly *) *)
    (* rename c into C'. *)
    (* clear H1. *)

    (* apply inr. *)
    (* exists (C', o). *)
    (* exists x2. *)
    (* split. *)
    (* apply p_env.updatedFuncProp; apply eq_refl. *)
    (* split. *)

    (* set (lem := proj1 (p_gamma.updatedFuncProp gamma  x sigma0 x) (eq_refl x)). *)
    (* rewrite lem in H0; inversion H0. rewrite H6 in *. *)
    (* rename sigma1 into sigma'; clear  H6 H0. *)
    (* rewrite H2 in H5; inversion H5; rewrite <- H1 in *. *)
    (* clear H1 H5. *)
    (* exact lem. *)
    (* exact H4. *)

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

    apply asm0.

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

    split.
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
    split.
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
    rewrite  öäåäö
    
    rewrite L_z_val in H0.
    
    
    
    set (new_4d := _3_b z tau new_4_a).
    unfold WF_Var in new_4d.
    rewrite new_4_cb in *.
    rewrite new__4_ca_ii in *.
    rewrite new_4_a in *.
    rewrite _6.

    (* 6 a *)
    induction envVar.
    
    apply inl. apply inl. reflexivity.
    case_eq (rn_eq_dec r o).
    intros r_o_eq dummy'. clear dummy' dummy.
    rewrite r_o_eq in *.
    
    set (lemm := proj1 (p_heap.updatedFuncProp H o (obj C (p_FM.newPartFunc flds FM_null)) o)
                         (eq_refl _)
            ).
    
    destruct new_4d.
    destruct s.
    inversion e.
    destruct s.
    destruct x0.
    destruct y.
    destruct a.
    inversion H0.
    rewrite -> H3 in *.
    clear o H3.
    rename r0 into o.
    clear r_o_eq r.
    clear H0.
    destruct H1.
    inversion H0.
    rewrite -> H3 in *.
    clear H3 tau.
    clear H0.
    
    
    destruct s.
    apply inl. apply inl.
    exact e.
    apply inl. apply inr.
    destruct s.
    destruct x0.
    exists (c, r).
    destruct y.
    TODO FINISH!!!
    intro.
    set (lem'''':= proj2 (p_env.fDomainCompat L z ) H0).
    firstorder.
    
    
        
    (* Section half_6 from paper: *)
    
    assert (p_env.updatePartFunc L x (envRef o) )
    
    
                     Gamma eff t L ann sigma,)
    
    set (_2_A := t)
    
    
    
    