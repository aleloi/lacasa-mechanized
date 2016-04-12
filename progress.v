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
Require Import progress_sf.

Require Import wf_env.

Import ConcreteEverything.


Section Progress.

  Variable P: Program.

  Definition subtypeP := subtype P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  Definition t_frame1' := t_frame1 P.
  Definition WF_Frame' := WF_Frame P.
  Definition WF_FS' := WF_FS P.

  Definition Reduction_SF' := Reduction_SF P .
  Definition Reduction_FS' := Reduction_FS P .
  Definition fieldsP := fields P.
  Definition TypeChecksP := TypeChecks P.
  Definition Heap_okP := Heap_ok P.
  Definition Heap_dom_okP := Heap_dom_ok P .

  Notation "( p +++ a --> b )" := (p_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o --> obj )" := (p_heap.updatePartFunc
                                              H o obj)
                                      (at level 0).

  Print Heap_type.

  Definition y_dereference e y : Prop :=
    match e with
      | FieldSelection y' f => y = y'
      | FieldAssignment y' f z => y = y'
      | MethodInvocation y' m z => y = y'
      | Open y' z t => y = y'
      | _ => False
    end.


  Require Import Coq.Lists.List.

  Theorem progress_thm :
    forall H FS,

      WF_FS' None H FS ->
      Heap_okP H ->
      Heap_dom_okP H ->
      FS <> nil -> (* replace with H, a |- FS *)

      (* exists reduction *)
      { H'_FS': Heap_type * (list ann_frame_type)
                              &
                              let (H', FS') := H'_FS' in 
                              Reduction_FS' (H, FS) (H', FS')
              
      } +

      (* frame stack has a single Var frame *)
      { x_l_L : VarName_type
                * annotation_type
                * Env_type
                    &
                    match x_l_L with
                      | (x, l, L) => 
                        FS = (ann_frame (sframe L (Var x))  l) :: nil
                    end
      } +

      (* null dereference *)

      { x_l_L_y_e_t_FS' :
          VarName_type
          * annotation_type
          * Env_type
          * VarName_type
          * ExprOrTerm
          * ExprOrTerm
          * (list ann_frame_type)
              &
              match x_l_L_y_e_t_FS' with
                | (x, l, L, y, e, t, FS') =>
                  (isTerm t) /\  (isExpr e) /\ (p_env.func L y = Some envNull ) /\
                  (y_dereference e y) /\
                  FS = (ann_frame
                          (sframe L (
                                    t_let x <- e t_in t
                                  ))  l) :: FS'
              end
      }.

    intros.
    destruct FS.
    induction (H2 (eq_refl _)).
    rename a into F; clear H2.
    assert {sigma : typecheck_type & WF_Frame' H F sigma }.
    inversion X.
    exists sigma; assumption.
    exists tau; assumption.
    
    destruct F as [frm l].
    destruct frm as [L' t].
    set (F := (ann_frame (sframe L' t) l)).
    fold F in X0, X.
    destruct X0 as [sigma WF_F].
    set (WF_F'' := WF_F).
    destruct WF_F as [H Gamma eff t' L'' ann sigma' tTerm typ_F_sigma].
    rename sigma' into sigma.
    clear L'.
    rename L'' into L'.
    clear t; rename t' into t.
    rename H0 into heap_okH; rename H1 into heap_dom_okH.
    destruct t.
    induction tTerm.
    destruct ann.
    apply inl.
    apply inl.
    exists (H, FS).
    apply E_Return2.
    
    rename v into y.
    assert ({envVal | p_env.func L' y = Some envVal}).
    inversion typ_F_sigma.
    clear H1 H2 H0 H4 gamma eff0 x sigma0 heap_dom_okH heap_okH X FS l .

    set (w' := fst w).
    apply (fun f => f y ) in w'.
    assert (In y (p_gamma.domain Gamma)).
    apply (p_gamma.in_part_func_domain _ _ sigma); assumption.
    apply (fun f => f H0) in w'.
    apply p_env.in_part_func_domain_conv; assumption.

    destruct X0 as [envVal L'y_eq].
    set (G := ann_frame (sframe L' (Var y)) (ann_var v0)).
    fold G in X.
    destruct FS.
    apply inl.
    apply inr.
    exists (y, (ann_var v0), L'); reflexivity.

    rename a into F.
    apply inl. apply inl.
    exists (H, updFrame F v0 envVal :: FS).
    apply E_Return1.
    assumption.

    induction tTerm.
    induction tTerm.
    induction tTerm.
    induction tTerm.
    induction tTerm.
    induction tTerm.
    rename L' into L.

    set (F := ann_frame (sframe L t_let v <- t1 t_in (t2)) ann).
    fold F in X, WF_F''.

    destruct t1.
    
    apply inl; apply inl.
    destruct (progress_SF_case_null
                P
                H L t2 v sigma ann WF_F'' heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.


    apply inl; apply inl.
    destruct (progress_SF_case_var
                P
                H L t2 v v0 sigma ann
                WF_F'' heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    
    (* Prove y in L: *)
    rename v0 into y.
    rename v into x.
    assert (In y (p_env.domain L)).
    clear WF_F'' tTerm heap_okH heap_dom_okH X FS.
    inversion typ_F_sigma.
    inversion X.
    clear H9 H10 H6 H8 H7 witn f0 x1 eff1 gamma0 H2 H5 H5 H4 H3 H1 H0 X0 X t tau.
    clear x0 sigma0 e eff0 gamma.
    apply fst in w.
    exact (w y (p_gamma.in_part_func_domain _ _ _ H11)).
    destruct (p_env.in_part_func_domain_conv _ _ H0).
    clear H0.

    destruct x0.
    apply inr.
    exists (x, ann, L, y, FieldSelection y f, t2, FS).
    split.
    inversion tTerm; assumption.
    split.
    simpl.
    auto.
    split.
    assumption.
    split.
    simpl.
    reflexivity.
    reflexivity.

    assert (p_env.func L y <> Some envNull).
    simplify_eq.
    rewrite H0 in e; discriminate.
    apply inl; apply inl.
    destruct (progress_SF_case_field
                P
                H L t2 x y f sigma ann
                WF_F'' H0 heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    assert (p_env.func L y <> Some envNull).
    simplify_eq.
    rewrite H0 in e; discriminate.
    apply inl; apply inl.
    destruct (progress_SF_case_field
                P
                H L t2 x y f sigma ann
                WF_F'' H0 heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    rename v0 into y.
    rename v into x.
    assert (In y (p_env.domain L)).
    clear WF_F'' tTerm heap_okH heap_dom_okH X FS.
    inversion typ_F_sigma.
    inversion X.
    clear H9 H10 H6 H8 H7 witn f0 x1 eff1 gamma0 H2 H5 H5 H4 H3 H1 H0 X0 X t tau H11.
    inversion X1.
    clear x0 sigma0 e eff0 gamma witn0 H5 H4 H0 H2 H1 witn f0 x1 eff1 gamma0.
    clear H13 X1 H12 D C y0.
    apply fst in w.
    exact (w y (p_gamma.in_part_func_domain _ _ _ H3)).
    destruct (p_env.in_part_func_domain_conv _ _ H0).
    clear H0.

    destruct x0.
    apply inr.
    exists (x, ann, L, y, FieldAssignment y f v1, t2, FS).
    split.
    inversion tTerm; assumption.
    split.
    simpl.
    auto.
    split.
    assumption.
    split.
    simpl.
    reflexivity.
    reflexivity.

    assert (p_env.func L y <> Some envNull).
    simplify_eq.
    rewrite H0 in e; discriminate.
    apply inl; apply inl.
    destruct (progress_SF_case_assign
                P
                H L t2 x y f v1 sigma ann
                WF_F'' H0 heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    assert (p_env.func L y <> Some envNull).
    simplify_eq.
    rewrite H0 in e; discriminate.
    apply inl; apply inl.
    destruct (progress_SF_case_assign
                P
                H L t2 x y f v1 sigma ann
                WF_F'' H0 heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
      destruct sf_config as [H' frame].
    
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    (* Method invocation *)
    admit.

    (* New *)
    apply inl; apply inl.
    destruct (progress_SF_case_new
                P
                H L c t2 v sigma ann
                WF_F'' heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
    destruct sf_config as [H' frame].
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    (* Box *)
    apply inl; apply inl.
    destruct (progress_SF_case_box
                P
                H L c t2 v sigma ann
                WF_F'' heap_okH heap_dom_okH)
      as [sf_config sf_reduction];
    destruct sf_config as [H' frame].
    exists (H', ann_frame frame ann :: FS).
    destruct frame.
    apply (E_StackFrame P H H').
    assumption.

    (* Open *)

    rename v0 into y.
    rename v1 into z.
    destruct tTerm as [t1Term t2Term].

    assert (
        (p_env.func L y = Some envNull) +
        {o : Ref_type & p_env.func L y = Some (envBox o) /\
             In o (p_heap.domain H)
        }) as L_props.
      

    clear F WF_F'' X t1Term t2Term heap_dom_okH FS l.
    inversion typ_F_sigma.
    clear H2 tau H5 t H3 eff0 H1 gamma H0 typ_F_sigma x X0 v e H4.
       
    inversion X.
    rewrite <- H2 in *; clear H2 H5 t H4 y0 H3 x eff0 H1 gamma H0 X1 X sigma1.
    inversion X0.
    clear H4 sigma1 H0 x H2 eff0 H1 gamma X0 sigma0 sigma eff ann.
    
    set (w' := fst w). 
    set ( lem := w' y (p_gamma.in_part_func_domain _ _ _ H3)).
    destruct (p_env.in_part_func_domain_conv _ _ lem).
    clear lem w'.

    apply snd in w.
    apply (fun f => f y (typt_box C) H3) in w.
    inversion w.
    destruct X.
    apply inl; assumption.
    destruct s; destruct x0; destruct y0; destruct a; destruct H1; rewrite H1 in H3; discriminate.
    destruct X; destruct x0; destruct y0; destruct a; destruct H1.
    apply inr. rename r into o. exists o.
    split; assumption.

    destruct L_props.
    apply inr.
    clear l.
    exists (v, ann, L, y, Open y z t1, t2, FS).
    split. assumption.
    split. auto.
    split. assumption.
    split. reflexivity.
    reflexivity.
    
    apply inl; apply inl.
    destruct s as [o L_y_o_prop].
    exists (H,
            (ann_frame (sframe (p_env.emptyPartFunc +++ z --> envBox o) t1) ann_epsilon) ::
            (ann_frame (sframe ( L +++ v --> (envBox o) ) t2)
                          ann) :: FS).
    apply (E_Open P H L).
    assumption.
    assumption.
    destruct L_y_o_prop.
    assumption.
    destruct L_y_o_prop.
    assumption.

    (* let let *)
    inversion tTerm.
    induction H0.

  Admitted.

End Progress.