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
  Definition TypeChecksP := TypeChecksTerm P.
  Definition Heap_okP := Heap_ok P.
  Definition Heap_dom_okP := Heap_dom_ok P .

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
      
      exists ( # (H +*+ o ↦ (obj C FM)),
               ( L +++ x ↦ envRef o ) , t ! ).
      apply (E_New _ _ _ _ _ _  _ _  flds). 
      assumption; clear H2 H3.
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
      
      exists ( # (H +*+ o ↦ (obj C FM)),
               ( L +++ x ↦ envBox o ) , t ! ).
      apply (E_Box _ _ _ _ _ _  _ _  flds).
      
      assumption; clear H2 H3.
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
      clear  H1 H0 X ann.
      inversion X0.
      clear H0 gamma H1 eff0 x0 H3 t0 H5 tau H2 e H4.
      inversion X.
      clear H1 eff0 x0 H4 sigma1 H2 H0 X X2 gamma X0.
      apply fst in X1.
      unfold gamma_env_subset in X1.
      apply (fun f => f y) in X1.
      apply (fun f => f (p_Γ.in_part_func_domain _ _ _ H3)) in X1.
      case_eq (p_env.func L y).
      intros L_y L_y_eq.
      exists L_y; reflexivity.
      intro.
      set (lem := p_env.fDomainCompat L y).
      firstorder.
      
      destruct X2 as [null_ref_box L_y_is_null_ref_box].
      
      exists ( # H , (L +++ x ↦ null_ref_box) , t ! ).
      apply E_Var.
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

      exists (# H, (L +++ x ↦ envNull), t !).
      apply E_Null.
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
      clear H6 H5.
      clear H0 H2  H4 L0 H3 t0 H4 ann0 sigma0 H3 H4.
      assert ({C | p_Γ.func Gamma y = Some (typt_class C)}).
      clear H1  X ann.
      inversion X0.
      clear  H0 gamma H1 eff0 x0 H3 t0 H5 tau H2 e H4 x X0 X2 sigma .
      inversion X.
      clear H0 eff0 x f0 H1 H2  H4 gamma H3 sigma0 X witn t f.
      exists C; assumption.
      destruct X2 as [C gamma_y_is_C].

      Require Import Coq.Lists.List.

      assert ({o | p_env.func L y = Some (envRef o) /\
                   In o (p_heap.domain H)
              }).

      destruct X1 as [subset L_gamma_compat].
      unfold gamma_env_subset in subset.
      apply (fun f => f y) in subset.
      apply (fun f => f (p_Γ.in_part_func_domain _ _ _ gamma_y_is_C)) in subset.
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
      destruct aaaa as [aaa1 aaa2].
      inversion aaa1.
      assumption.
      
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]. destruct aaaa as [aaaaa bbbbb].
      rewrite gamma_y_is_C in bbbbb.
      discriminate.

      destruct L_gamma_compat.
      destruct s.
      firstorder.
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct aaaa as [a5 b5].
      rewrite L_y_eq in a5; discriminate.

      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct aaaa as [aaaaa bbbbb].
      rewrite gamma_y_is_C in bbbbb.
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
      destruct bbb as [aaaa bbbb]; destruct aaaa as [aaaaa bbbbb].
      rewrite gamma_y_is_C in bbbbb.
      inversion aaaaa.
      rewrite <- H2 in *.
      inversion bbbbb.
      rewrite <- H3 in *.
      clear aaaaa cc bbbbb H3.
      rewrite L_y_i_o in H2; inversion H2.
      rewrite  H3 in *.
      rename H3 into ooo_equal.
      clear  H2.
      exists (heap_typeof H oo aaa).
      split.

      set (C := heap_typeof H o o_in_H).
      destruct (heap_typeof_impl P H o C o_in_H (eq_refl _))
        as [FM H_o_value].
      rewrite ooo_equal in H_o_value.
      symmetry.
      apply (heap_typeof_same P _ _ _ FM H_o_value).
      unfold wf_env.subtypeP in bbbb.
      inversion bbbb.
      clear D H0 H2      .
      assumption.
      
      destruct s as [aa bb]; destruct aa as [cc oo]; destruct bb as [aaa bbb];
      destruct bbb as [aaaa bbbb]; destruct aaaa as [aaaaa bbbbb].
      rewrite gamma_y_is_C in bbbbb.
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
        ( L +++ x ↦ (fm2env fmVal) ) , t ! ).

      apply (E_Field _ _ _ o _ _ _ _
                     C FM _ L_y_i_o H_o_value
                     FM_f
            ).
    Qed.


    Notation "y ∘ f ⟵ z" := (FieldAssignment y f z) (at level 0).

    Notation "a ⟿ b" :=  (Reduction_SF' a b) (at level 0).
    Notation " ⊢ H" := (Heap_okP H) (at level 0).
    Notation " ⊩ H" := (Heap_dom_okP H) (at level 0).
    Notation "( Γ , ef ⊩' t ▷ σ )" := (TypeChecksTerm P Γ ef t σ) (at level 0).
    Notation "( Γ , ef ⊩'' e ▷ σ )" := (TypeChecksExpr P Γ ef e σ) (at level 0).
    
    Theorem progress_SF_case_assign :
    forall H L t x y f z sigma ann,
      WF_Frame' H (ann_frame
                     (sframe L (t_let x <- (FieldAssignment y f z) t_in t))
                     ann) sigma ->
      p_env.func L y <> Some envNull ->
      ⊢ H ->
      ⊩ H ->
      { frame : sfconfig_type
                  & 
                  (# H, L, (t_let x <- (y ∘ f ⟵ z) t_in t) !) ⟿ frame}.
      
      intros H L t x y f z sigma ann wf_frame L_y_not_null heap_ok_H heap_dom_ok_H.
      set (F := [L, t_let x <- y ∘ f ⟵ z t_in t]^ ann).
      fold F in wf_frame.
      clear heap_ok_H.
      inversion_clear wf_frame as [ dummy_ Γ ef ].
      rename X into typ_sigma.
      rename X0 into wf_H_Γ_L.
      rename sigma into σ.
      clear F ann.
      unfold wf_env.TypeChecksP in typ_sigma.
      inversion_clear typ_sigma as [a_dummy b_dummy c_dummy τ  | ].
      rename X into typ_τ.
      clear X0.
      (* rename X0 into Γ'_typ_σ. *)
      (* set (Γ' := (Γ ⊍ x ↦ τ)). *)
      (* fold Γ' in Γ'_typ_σ. *)
      inversion_clear typ_τ.
      rename H0 into Γ_z_is_C.
      rename X into y_f_is_D.
      clear X0 τ.
      (* rename X0 into C_sub_D. *)
      (* unfold typing.subtypeP in C_sub_D. *)
      (* inversion_clear C_sub_D. *)
      (* rename H0 into C_sub_D. *)
      inversion y_f_is_D.
      clear gamma x0 H1 H2 eff H0 H4 f0 witn0.
      rename C0 into C'.
      rename H3 into ΓyC'.
      rename H5 into C'_field.
      set (D' := (typing.ftypeP P C' f witn)).
      destruct C'_field.
      rename D' into D.
      fold D in (* C_sub_D,  *) y_f_is_D.

      set (wf_H_Γ_L' := wf_H_Γ_L).

      assert ({o | p_env.func L y = Some (envRef o)
                   /\
                   In o (p_heap.domain H)
              }) as L_y_o.
      { (* L y = o, o in H *) 
        clear (* C_sub_D *) Γ_z_is_C C heap_dom_ok_H 
              z t
        .
        apply fst in wf_H_Γ_L'.
        apply (fun f => f y) in wf_H_Γ_L'.
        assert (In y (p_Γ.domain Γ)) as y_in_Γ.
        apply (p_Γ.in_part_func_domain _ _ _ ΓyC').
        apply (fun f => f y_in_Γ) in wf_H_Γ_L'.
        clear y_in_Γ.

        destruct (p_env.in_part_func_domain_conv _ _  wf_H_Γ_L') as
            [envVal envValEq].
        
        

        apply snd in wf_H_Γ_L.
        apply (fun f => f y (typt_class C') ΓyC' ) in wf_H_Γ_L.
        
        destruct wf_H_Γ_L as [L_y_not_box | L_y_box ].
        { (* L y not box *)
          destruct L_y_not_box as [L_y_is_null |
                                   [ [_ o'] [o'_in_H [[L_y_is_o' _] _]  ] ]  ].

          { (* L y = null *) 
            rewrite L_y_is_null in L_y_not_null;  exfalso; apply L_y_not_null;
            reflexivity.
          }
          { (* L y = o *)
            exists o'; exact ( conj L_y_is_o' o'_in_H).
          }
        }
        { (* L y = b(o) *)
          destruct L_y_box as [ [C'' _] [_ [[_ ΓyBox] _]]].
          rewrite ΓyC' in ΓyBox; inversion ΓyBox.
        }
        
      }

      destruct L_y_o as [o [L_y_o o_in_H]].

      destruct (p_heap.in_part_func_domain_conv H o o_in_H) as
          [[C'' FM''] H_o_C_FM].

      assert ({o | p_env.func L z = Some (envRef o)
                   /\
                   In o (p_heap.domain H)
              } + (p_env.func L z = Some envNull)) as L_z.
      { (* L z = o, o in H *) 
        clear (* C_sub_D *)  heap_dom_ok_H  
              t
        .
        apply fst in wf_H_Γ_L'.
        apply (fun f => f z) in wf_H_Γ_L'.
        assert (In z (p_Γ.domain Γ)) as z_in_Γ.
        { (* z in Gamma *)
          apply (p_Γ.in_part_func_domain _ _ _ Γ_z_is_C).
        }
        apply (fun f => f z_in_Γ) in wf_H_Γ_L'.
        clear z_in_Γ.
        
        destruct (p_env.in_part_func_domain_conv _ _  wf_H_Γ_L') as
            [envVal envValEq].
        
        apply snd in wf_H_Γ_L.
        apply (fun f => f z (typt_class C) Γ_z_is_C ) in wf_H_Γ_L.
        
        destruct wf_H_Γ_L as [L_z_not_box | L_z_box ].
        { (* L z not box *)
          destruct L_z_not_box as [L_z_is_null |
                                   [ [_ o'] [o'_in_H [[L_z_is_o' _] _]  ] ]  ].

          { (* L z = null *)
            apply inr; exact L_z_is_null.
          }
          { (* L y = o *)
            apply inl; exists o'; exact ( conj L_z_is_o' o'_in_H).
          }
        }
        { (* L y = b(o) *)
          destruct L_z_box as [ [C''' _] [_ [[_ ΓzBox] _]]].
          rewrite Γ_z_is_C in ΓzBox; inversion ΓzBox.
        }
      }

      clear  L_y_not_null   Γ_z_is_C y_f_is_D.
      
      assert (C'' ⪯ C' ) as heap_typ_sub_typ_type.

      { (* C'' ⪯ C' *)
        apply snd in wf_H_Γ_L'.
        apply (fun f => f y (typt_class C') ΓyC' ) in wf_H_Γ_L'.
        
        destruct wf_H_Γ_L' as [L_y_not_box | L_y_box ].
        { (* L y not box *)
          destruct L_y_not_box as [L_y_is_null |
                                   [ [C''' o']
                                       [o'_in_H [[L_y_is_o' ΓyC'''] subC']  ] ]  ].

          { (* L y = null *)
            rewrite L_y_is_null in L_y_o; discriminate.
          }
          { (* L y = o *)
            rewrite L_y_o in L_y_is_o'; inversion L_y_is_o' as [o_eq];
            destruct o_eq; clear L_y_is_o'.
            rewrite ΓyC' in ΓyC'''; inversion ΓyC''' as [C_equal];
            destruct C_equal.
            inversion_clear subC'. rename H0 into typeof_sub_C'.
            destruct (heap_typeof_impl P _ o
                                       (heap_typeof H o o'_in_H)
                                       o'_in_H
                                       (eq_refl _ )
                     ) as [FM' H_o'_typeof].
            rewrite  H_o_C_FM in H_o'_typeof;
              inversion H_o'_typeof  as [[C''_typeof dummy] ].
            exact typeof_sub_C'.
          }
        }
        { (* L y = b(o) *)
          destruct L_y_box as [ [C''' _] [_ [[_ ΓyBox] _]]].
          rewrite ΓyC' in ΓyBox; inversion ΓyBox.
        }
      }
      
      assert (In f (p_FM.domain FM'')) as f_in_FM.
      {
        clear x t z σ  C D wf_H_Γ_L' o_in_H L_z.
        set (f_fld_C'' := field_subclass P C'' C' f witn heap_typ_sub_typ_type).
        apply (fun f => f o C'' FM'') in heap_dom_ok_H .
        apply (fun f => f H_o_C_FM) in heap_dom_ok_H.
        exact (fld_in_flds P C'' f (p_FM.domain FM'')
                                f_fld_C'' heap_dom_ok_H
            ).
      }

      assert ({envVal | p_env.func L z = Some envVal
                        /\ is_not_box envVal
              }) as L_env_val.
      { (* L z = envVal, envVal not box *)
        destruct L_z as [ [o' [L_z_o' _]]  | L_z_null ].
        {
          exists (envRef o').
          split.
          { exact L_z_o'.  }
          { simpl. auto. }
        }
        {
          exists envNull; split.
          {  exact L_z_null.      }
          { simpl. auto. }
        }
      }
      
      destruct L_env_val as [env_val [L_z_envVal not_box_envVal]].

      set (frame_reduces := E_Assign P x y z o f t H L C'' FM'' env_val
                                     not_box_envVal L_y_o H_o_C_FM
                                     f_in_FM L_z_envVal
          ).
      exists ( # (H +*+ o
               ↦ obj C''
               (p_FM.updatePartFunc FM'' f
                                    (env2fm env_val not_box_envVal))),
          (L +++ x ↦ env_val), t ! ).
      exact frame_reduces.
    Qed.

End Progress_SF.

