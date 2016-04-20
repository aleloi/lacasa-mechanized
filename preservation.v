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
  Definition TypeChecksP := TypeChecksTerm P.
  Definition TypeChecksExprP := TypeChecksExpr P.
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
    exists (p_Γ.updatePartFunc gamma v sigma0); auto;
    rewrite H9 in *; auto.
  Qed.

  Local Open Scope type_scope.


  Theorem preservation_case_var :
    forall H L x y t sigma ann envVar,
      WF_Frame' H (ann_frame (sframe L (t_let x <- Var y t_in (t))) ann) sigma ->
      p_env.func L y = Some envVar ->
      WF_Frame' H (ann_frame (sframe (p_env.updatePartFunc L x envVar) t) ann) sigma.
    intros.
    rename H0 into L_y_value.
    
    inversion X.
    clear X.
    clear H4 t0 H5  H1 H2  L0 ann0 sigma0 H0 H3.
    (* rename H6 into let_t_is_term. *)
    rename X0 into Gamma_type_let.
    rename X1 into wf_env_frame.
    
    inversion Gamma_type_let.
    clear Gamma_type_let.
    clear gamma H0 x0 H3 eff0 H1 t0 H5 H2 tau H4 e.
    rename X into Gamma_type_var_y; rename X0 into Gamma'_type_t.
    set (Gamma' := (p_Γ.updatePartFunc Gamma x sigma0)).
    fold Gamma' in Gamma'_type_t.
    
    (* split. *)
    set (L' := (p_env.updatePartFunc L x envVar)).
    apply (t_frame1' H  Gamma' eff t
                     L' ann sigma).
    exact Gamma'_type_t.
    clear Gamma'_type_t.
    
    split.
    destruct wf_env_frame.
    apply (subset_preserved _ _ _ _ _ g).
    intros.
    rename H0 into Gamma'_x.
    elim (v_eq_dec x x0).
    intro; rewrite <- a in *; clear a.

    inversion Gamma_type_var_y.
    clear H4 H2 H0 H1 sigma2 gamma eff0 Gamma_type_var_y eff.
    
    rename H3 into Gamma_y_value.

    set (wf_var_y := snd wf_env_frame y sigma0 Gamma_y_value).
    
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
    rename L_y_value into _3_b_i_A. 
    induction  wf_var_y.
    induction a. (* case L(y) = null in WF-var *)
    rewrite a in _3_b_i_A; discriminate.

    induction b;  destruct x2. (* case L(y) = o', H(o') = <C, FM> in WF-var*)
    induction p.
    destruct p as [[Ly_value Gamma_y_value' ] heap_Γ_y_subtype ].
    rewrite (_3_b_i_A) in *; inversion Ly_value.
    destruct H1.
    rename c into C'.
    clear Ly_value.

    apply inl. apply inr.
    exists (C', o).
    exists x2.
    split. split.
    apply p_env.updatedFuncProp; apply eq_refl.

    set (lem := proj1  (p_Γ.updatedFuncProp Gamma  x sigma0 x) (eq_refl x)).
    fold Gamma' in lem.
    rewrite lem in Gamma'_x; inversion Gamma'_x; rename H1 into sigma01_eq;
    rewrite sigma01_eq in *.
    rename sigma1 into sigma'; clear sigma01_eq Gamma'_x.
    rewrite Gamma_y_value' in Gamma_y_value; inversion Gamma_y_value;
    rename H1 into C'_sigma; rewrite <- C'_sigma in *.
    clear C'_sigma sigma'. assumption.
    assumption.

    destruct b;
      destruct x2;
    destruct y0; destruct p as  [[L_y_value Gamma_y_value'] heap_sub_c].

    rewrite (_3_b_i_A) in *; inversion L_y_value.

    (* 3 c, L(y) = b(o)*)
    rename L_y_value into _3_c.
    rename r into o.
    destruct wf_env_frame as [_3_c_i_A _3_c_i_B].
    rename Gamma_y_value into _1_b.
    rename sigma0 into sigma'.
    simpl in wf_var_y.

    rename wf_var_y into _3_c_ii.
    induction (_3_c_ii).
    induction a. (* 3. c. iii. *)
    rewrite a in _3_c; discriminate. (* 3. c. iv.*)
    induction b; destruct x2;
    destruct p as [r_in_H [[L_y_value Gamma_y_value] gamma_heap_y_r_c] ].
    rename L_y_value into _3_c_v.
    rewrite _3_c_v in _3_c; discriminate. (* 3. c. v. *)

    

    destruct b; destruct x2. destruct y0. destruct p as
        [[L_y_value Gamma_y_value] C'_sub_c].
                             
    
    set (C' := (heap_typeof H r x2)); fold C' in C'_sub_c.
    rewrite _3_c in L_y_value; inversion L_y_value.
    rename x0 into z.
    rename sigma1 into tau.
    rename H1 into refs_o_r_equal.

    (* intro. *)
    (* 3 box *)
    destruct refs_o_r_equal.
    (* rewrite  H5 in *. clear H5 o. rename r into o. *)
    clear L_y_value.
    unfold WF_Var.
    rewrite Gamma'_x.
    apply inr.
    exists (c, o).
    exists x2.
    split.
    simpl. split.
    exact (proj1 (p_env.updatedFuncProp L x (envBox o) x) (eq_refl _)).
    
    simpl in Gamma'_x.
    rewrite _1_b in Gamma_y_value.
    inversion Gamma_y_value.
    rename H1 into sigma'_typt_box_c.
    symmetry in sigma'_typt_box_c.
    destruct sigma'_typt_box_c.
    set (lem := (proj1 (p_Γ.updatedFuncProp Gamma x (typt_box c) x) (eq_refl _))).
    fold Gamma' in lem.
    simpl in lem.
    rewrite lem in Gamma'_x.
    inversion Gamma'_x.
    rename H1 into typt_box_c_tau.
    f_equal.
    exact C'_sub_c. 

    clear Gamma_type_var_y  eff ann.
    
    (* 4 *)
    rename Gamma'_x into Gamma'z.
    intro x_neq_x0.
    rename x0 into z.
    rename sigma1 into tau.
    rename sigma0 into sigma'.
    assert (p_Γ.func Gamma z = Some tau) as _4_a.
    rewrite <- Gamma'z.
    symmetry.
    apply p_Γ.updatedFuncProp. firstorder.

    destruct wf_env_frame as [ _4_c_i _4_c_ii].
    set (_4_d := _4_c_ii z tau _4_a).
    unfold WF_Var.
    rewrite Gamma'z.
    Require Import Coq.Lists.List.
    assert (In z (p_Γ.domain Gamma)) as _4_ca.
    set (lem := p_Γ.fDomainCompat Gamma z).
    set (in_or_not := in_dec v_eq_dec z (p_Γ.domain Gamma)).
    firstorder; rename H0 into Gamma_z_None;
    rewrite Gamma_z_None in _4_a; discriminate.

    set (lem''' := _4_c_i z _4_ca).
    case_eq (p_env.func L z).
    intros envVar' _4_ca_ii.

    assert (p_env.func L' z = Some envVar') as _4_cb.
    transitivity (p_env.func L z).
    apply p_env.updatedFuncProp. firstorder.
    exact _4_ca_ii.
    unfold WF_Var in _4_d.
    rewrite _4_cb in *.
    rewrite _4_ca_ii in _4_d.
    rewrite _4_a in _4_d.
    exact _4_d.

    intro L_z_value.
    set (lem'''':= proj2 (p_env.fDomainCompat L z ) L_z_value).
    
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
    
    apply (t_frame1' H (p_Γ.updatePartFunc Gamma x sigma' )
                    eff t
                    (p_env.updatePartFunc L x envNull) ann sigma).
    exact _4_b.

    unfold WF_Env.
    split.
    
    exact (subset_preserved Gamma L x sigma' envNull _6_a).

    intros z tau _8.
    elim (v_eq_dec x z).
    intro x_is_z; rewrite <- x_is_z in *; clear x_is_z.
    (* assert (p_Γ.func (p_Γ.updatePartFunc Gamma x sigma') x = Some sigma') as _10_a. *)

    (* exact (proj1 (p_Γ.updatedFuncProp Gamma  x sigma' x) (eq_refl x)). *)
    (* rewrite -> _10_a in _8; inversion _8. rewrite <- H1 in *; clear H1 tau _8. *)
    (* unfold WF_Var. *)
    apply inl.
    apply inl.
    exact (proj1 (p_env.updatedFuncProp L  x  envNull x) (eq_refl x)).

    intro x_neq_z. 
    assert (p_Γ.func Gamma z = Some tau) as new_4_a.
    rewrite <- _8.
    symmetry.
    apply (proj2 (p_Γ.updatedFuncProp Gamma x sigma' z)).
    firstorder.
    
    (* set (new__4_d := _6_b z tau _4_a). *)
    unfold WF_Var.
    
    (* rewrite H0. *)
    
    
    
    (* Require Import Coq.Lists.List. *)
    assert (In z (p_Γ.domain Gamma)) as new_4_ca.
    set (lem := p_Γ.fDomainCompat Gamma z).
    set (in_or_not := in_dec v_eq_dec z (p_Γ.domain Gamma)).
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
      fieldsP C flds ->
      WF_Frame'
        (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))
        (ann_frame (sframe (p_env.updatePartFunc L x (envRef o)) t) ann) sigma.
  Admitted.


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
    rewrite <- H4 in *.
    clear H4 H5 H'a_is_obj lem C0 FM. 

    rewrite (p_FM.newPartFuncDomain flds FM_null).
    unfold heap.fieldsP.
    unfold fieldsP in H2.

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
    rewrite H3 in FM_o''_is_some.
    discriminate.

    set (lem'' := proj1 lem f_in_flds).
    rewrite lem'' in FM_o''_is_some; discriminate.
    assumption.

    assert (o' <> o). firstorder.

    set (lem := proj2 (p_heap.updatedFuncProp
                         H o obj' o')
                      H3
        ).
    clear are_eq.
    fold H' in lem.


    destruct X.
    clear Gamma eff t0 L0 ann0 sigma t1 w H2.
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
    clear lem H'a_is_obj f_witn C0 C''_sub_ftype FM FM_f_eq o' H3 f.

    destruct (heap_typeof_impl P H o'' C'' o''_in_H (eq_refl _))
      as [FM'' Ho''].
    rewrite Ho'' in lemlem; symmetry in lemlem.
    apply (heap_typeof_same P _ _ _ FM''); assumption.
    rewrite H2; assumption.
    unfold heap.fieldsP.
    clear H' lem H3 obj' H1 H3.
    exact (heap_dom_ok o' C0 FM H'a_is_obj).
  Qed.


  Theorem preservation_case_box_heap :
    forall H L sigma ann t C x (o: p_heap.A) flds,
      forall (heap_dom_ok: Heap_dom_okP H),
        WF_Frame' H (ann_frame (sframe L t_let x <- Box C t_in (t)) ann) sigma ->
        Heap_okP H ->
        ~ In o (p_heap.domain H) ->
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
    rewrite <- H4 in *.
    clear H4 H5 H'a_is_obj lem C0 FM. 

    rewrite (p_FM.newPartFuncDomain flds FM_null).
    unfold heap.fieldsP.
    unfold fieldsP in H2.

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
    rewrite H3 in FM_o''_is_some.
    discriminate.

    set (lem'' := proj1 lem f_in_flds).
    rewrite lem'' in FM_o''_is_some; discriminate.
    assumption.

    assert (o' <> o). firstorder.

    set (lem := proj2 (p_heap.updatedFuncProp
                         H o obj' o')
                      H3
        ).
    clear are_eq.
    fold H' in lem.


    destruct X.
    clear Gamma eff t0 L0 ann0 sigma  t1 w H2.
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
    clear lem H'a_is_obj f_witn C0 C''_sub_ftype FM FM_f_eq o' H3 f.

    destruct (heap_typeof_impl P H o'' C'' o''_in_H (eq_refl _))
      as [FM'' Ho''].
    rewrite Ho'' in lemlem; symmetry in lemlem.
    apply (heap_typeof_same P _ _ _ FM''); assumption.
    rewrite H2; assumption.
    unfold heap.fieldsP.
    clear H' lem H3 obj' H1 H3.
    exact (heap_dom_ok o' C0 FM H'a_is_obj).
  Qed.
  
  Theorem preservation_case_box :
    forall H L sigma ann t C x o flds,
      WF_Frame' H (ann_frame (sframe L t_let x <- Box C t_in (t)) ann) sigma ->
      Heap_okP H ->
      ~ In o (p_heap.domain H) ->
      fieldsP C flds ->
      WF_Frame'
        (p_heap.updatePartFunc H o (obj C (p_FM.newPartFunc flds FM_null)))
        (ann_frame (sframe (p_env.updatePartFunc L x (envBox o)) t) ann) sigma.
    Admitted.

Theorem preservation_case_select :
    forall H L sigma ann x y f t C FM fmVal o,
      WF_Frame' H (ann_frame (sframe L t_let x <- FieldSelection y f t_in (t)) ann) sigma ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_FM.func FM f = Some fmVal ->
      WF_Frame'
        H
        (ann_frame (sframe (p_env.updatePartFunc L x (fm2env fmVal)) t) ann) sigma.
  Admitted.


Theorem preservation_case_assign H L x y f z t C FM o sigma envVal ann:
    forall witn: is_not_box envVal,
      WF_Frame' H (ann_frame (sframe L t_let x <- (FieldAssignment y f z) t_in (t)) ann) sigma ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_env.func L z = Some envVal ->
      (WF_Frame'
         (p_heap.updatePartFunc H o
                                (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))
         (ann_frame (sframe (p_env.updatePartFunc L x envVal ) t) ann) sigma) *
      (Heap_okP (p_heap.updatePartFunc H o
                                       (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))
      ).
  Admitted.
  
  Theorem preservation_case_assign_heap H L x y f z t C FM o sigma envVal ann:
    forall witn: is_not_box envVal,
      WF_Frame' H (ann_frame (sframe L t_let x <- (FieldAssignment y f z) t_in (t)) ann) sigma ->
      Heap_okP H ->
      p_env.func L y = Some (envRef o) ->
      p_heap.func H o = Some (obj C FM) ->
      p_env.func L z = Some envVal ->
      (* isTerm t -> *)
      (Heap_dom_okP (p_heap.updatePartFunc
                   H o
                   (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))
      ).
  Admitted.
  

  (*
1 subgoal, subgoal 1 (ID 8710)
  
  P : Program
  H : p_heap.PartFunc
  H' : Heap_type
  L, L' : Env_type
  t' : ExprOrTerm
  sigma : typecheck_type
  ann : annotation_type
  heap_dom_ok : Heap_dom_okP H
  t : ExprOrTerm
  x : VarName_type
  y, z, f : p_Γ.A
  X : WF_Frame' H
        (ann_frame (sframe L t_let x <- FieldAssignment y f z t_in (t)) ann)
        sigma
  asm0 : Heap_okP H
  X0 : Reduction_SF' ( # H, L, t_let x <- FieldAssignment y f z t_in (t) ! )
         ( # H', L', t ! )
  o : Ref_type
  H0 : p_heap.PartFunc
  L0 : p_env.PartFunc
  C : class
  FM : FM_type
  envVal : env_Range_type
  witn : is_not_box envVal
  H7 : isTerm t
  H10 : p_env.func L y = Some (envRef o)
  H11 : p_heap.func H o = Some (obj C FM)
  H12 : In f (p_FM.domain FM)
  H13 : p_env.func L z = Some envVal
  H1 : H0 = H
  H2 : L0 = L
  H6 : p_heap.updatePartFunc H o
         (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))) = H'
  H8 : p_env.updatePartFunc L x envVal = L'
  ============================
   Heap_dom_okP
     (p_heap.updatePartFunc H o
        (obj C (p_FM.updatePartFunc FM f (env2fm envVal witn))))


*)


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
    rewrite <- H8 in *; clear L0 H8 H3.
    rewrite <- H6 in *; rewrite <- H9 in *; clear  H9 H6.
    rewrite <- H5 in *; clear H5.
    rewrite <- H4 in *; clear H4.
    
    split.
    split.

    Check preservation_case_var.
    exact (preservation_case_var H L x y t sigma ann null_ref_box X H2).
    assumption.
    assumption.
    
    (* Case t = let y = Null in t' *)
    
    rewrite  H9 in *; clear H9  t H6.
    rewrite <- H8 in *; clear H8.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H5 in *; clear e H5.
    rewrite <- H4 in *; clear H4.
    clear H3  L0 H0 H2.
    clear L'.
    rename t' into t.

    rename X into asm1.
    rename asm0 into asm2.
    rename X0 into asm0.
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

    rewrite -> H9 in *; clear H9 .
    rewrite <- H6 in *; clear H6 t'.
    rewrite <- H8  in *; clear L' H8.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H5 in *; clear e H5.
    rewrite <- H3 in *; clear H3 v.
    clear H2 L0 H0 H1.
    rewrite H11 in *; clear H11.

    split.
    split.
       
    exact (preservation_case_new H L sigma ann t C x o flds asm2 asm3 H4 H10  ).
    set (FM' := (p_FM.newPartFunc flds FM_null)).
    set (obj' :=(obj C FM')).
    set (H' := (p_heap.updatePartFunc H o obj')).
    apply (preservation_case_new_heap H L sigma ann t C x o flds heap_dom_ok
                                      asm2 asm3  H4 H10
          ).
    apply (preservation_case_new_heap H L sigma ann t C x o flds heap_dom_ok
                                      asm2 asm3 H4 H10
          ). 

    
    
    (* Case let x = Box C in t*)
    rewrite <- H6 in *; clear H6.
    rewrite <- H9 in *; clear H9 t' .
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H5 in *; clear e H5.
    rewrite <- H3 in *; clear H3 v.
    clear H2 L0 H1 H0.
    rewrite H11 in *; clear H11 FM.
    split. split.
    apply (preservation_case_box H L sigma ann t C x o flds X asm0 H4 H10 ).

    (* TWO ADMITS BELOW: change to the following. *)
    apply (preservation_case_box_heap H L sigma ann t C x o flds heap_dom_ok
                                      X asm0 H4 H10
          ).
    apply (preservation_case_box_heap H L sigma ann t C x o flds heap_dom_ok
                                      X asm0 H4 H10
          ).


    (* Case SELECT, let x = y.f in t *)
    split. split.

    rewrite <- H6 in *; clear H6 .
    rewrite <- H9 in *; clear H9 t'.
    rewrite <- H8 in *; clear H8 L'.
    rewrite <- H7 in *; clear H7 H'.
    rewrite <- H5 in *; clear H5 e.
    rewrite <- H3 in *; clear H3 v.
    clear L0 H0 H2 H1.
    apply (preservation_case_select H L sigma ann x y f t C FM fmVal o X asm0  H4
                                    H10 H11
          ).
    rewrite <- H7; exact asm0.
    rewrite <- H7; exact heap_dom_ok.

    (* Case ASSIGN, let x = (y.f = z) in t *)

    rewrite <- H6 in *.
    rewrite <- H9 in *.
    clear H9.

    rewrite <- H3 in *.
    clear v H3.
    
    rewrite <- H4 in *.
    clear H4 e.
    split.

    exact (preservation_case_assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ X asm0 H5
                                     H10 H12
          ).
    exact (preservation_case_assign_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X asm0 H5
                                    H10 H12
          ).
  Qed.

  
End Preservation.