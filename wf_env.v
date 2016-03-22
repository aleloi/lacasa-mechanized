Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import typing.
Require Import namesAndTypes.

Import ConcreteEverything.

Section WF_Env.

  Import Coq.Lists.List.

  Definition gamma_env_subset (gamma: Gamma_type) (L: Env_type) :=
    forall x,
      In x (p_gamma.domain gamma) ->
      In x (p_env.domain L).

  Theorem in_dec_equivalence (A: Type) (eq_dec: forall (x y: A),
                                                 {x = y} + {x <> y}
                                      ) :
    forall x l1 l2,
      (@In A x l1 <-> In x l2) <-> (~ In x l1 <-> ~ In x l2).
    intros.
    set (leml1 := in_dec eq_dec x l1).
    set (leml2 := in_dec eq_dec x l2).
    firstorder.
  Defined.
    

  Theorem subset_preserved gamma L x sigma envVal :
    gamma_env_subset gamma L ->
    gamma_env_subset (p_gamma.updatePartFunc gamma x sigma )
                     (p_env.updatePartFunc L x envVal).
    intros subset x'.
    intro.
    set (lem_gamma := p_gamma.updatedFuncProp gamma x sigma x').
    set (lem_env := p_env.updatedFuncProp L x envVal x').
    
    elim (v_eq_dec x' x).
    intro; rewrite a in *; clear a.
    set (lem_env_x := (proj1 lem_env) (eq_refl x)).
    set (lem_upd_env := proj1 (p_env.fDomainCompat (p_env.updatePartFunc L x envVal) x)).
    set (in_or_not := in_dec v_eq_dec x (p_env.domain (p_env.updatePartFunc L x envVal))).
    elim in_or_not.
    auto.
    intro.
    set (not_in := lem_upd_env b).
    rewrite not_in in lem_env_x; discriminate.

    (* x != x'
     * Proof structure:
     *    Then x' in dom(Gamma) <--> x' in dom(Gamma[x |-> sigma])
     *         x' in dom(L) <--> x' in dom(L[x |-> envVal])
     *)
    intro x_neq.
    assert (In x' (p_gamma.domain gamma) <-> In x' (p_gamma.domain
                                                      (p_gamma.updatePartFunc gamma x sigma))).
    apply (proj2 (in_dec_equivalence p_gamma.A v_eq_dec x' _ _)).
    set (lem_gamma' := (proj2 lem_gamma) x_neq).
    set (lem_gamma_upd_equiv
         := proj2 (p_gamma.fDomainCompat (p_gamma.updatePartFunc gamma x sigma) x')).
    set (lem_gamma_equiv := proj2 (p_gamma.fDomainCompat gamma x')).
    firstorder.

    assert (In x' (p_env.domain L) <-> In x' (p_env.domain
                                                      (p_env.updatePartFunc L x envVal))).
    apply (proj2 (in_dec_equivalence p_env.A v_eq_dec x' _ _)).
    set (lem_env' := (proj2 lem_env) x_neq).
    set (lem_env_upd_equiv
         := proj2 (p_env.fDomainCompat (p_env.updatePartFunc L x envVal) x')).
    set (lem_env_equiv := proj2 (p_env.fDomainCompat L x')).
    firstorder.
    firstorder.    
  Qed.
    
        
    

  Import Coq.Lists.List.

  
  Variable P: Program.
  
  Definition subtypeP := subtype P.

  Definition TypeChecksP := TypeChecks P.

  Local Open Scope type_scope.

  
  Definition WF_Var (H: Heap_type) (Gamma: Gamma_type) (L: Env_type) (x: VarName_type):=
    (p_env.func L x = Some envNull) +
    {C_o |
     match C_o with
       | (C, o) => {witn |
                    p_env.func L x = Some (envRef o) /\
                    p_gamma.func Gamma x = Some (typt_class C) /\
                    subtypeP (typt_class (heap_typeof H o witn)) (typt_class C)
                   }
     end} +
    {C_o |
     match C_o with
       | (C, o) => {witn |
                    p_env.func L x = Some (envBox o) /\
                    p_gamma.func Gamma x = Some (typt_box C) /\
                    subtypeP (typt_class (heap_typeof H o witn)) (typt_class C)
                   }
     end}.

  Definition WF_Env H Gamma L :=
    gamma_env_subset Gamma L *
    forall x sigma,
      p_gamma.func Gamma x = Some sigma ->
      WF_Var H Gamma L x.

  

  Inductive WF_Frame : Heap_type -> ann_frame_type -> typecheck_type -> Type :=
  | t_frame1 : forall H Gamma eff t L ann sigma,
                isTerm t ->
                TypeChecksP Gamma eff t sigma ->
                WF_Env H Gamma L ->
                WF_Frame H (ann_frame (sframe L t) ann) sigma.

  Inductive WF_Frame_ann : Heap_type -> ann_frame_type -> typecheck_type -> VarName_type ->
                           typecheck_type -> Type :=
  | t_frame2 : forall H Gamma eff t L ann sigma x tau,
                 isTerm t ->
                 TypeChecksP (p_gamma.updatePartFunc Gamma x tau) eff t sigma ->
                 WF_Env H Gamma L ->
                 WF_Frame_ann H (ann_frame (sframe L t) ann) sigma x tau.

  Notation "( H , x , tau ## F @@ sigma )" := (WF_Frame_ann H F sigma x tau).

  Definition FS_ann_type := option (VarName_type * typecheck_type).

  
  Inductive WF_FS : FS_ann_type -> Heap_type -> list (ann_frame_type) -> Type :=
    
  | T_EmpFS : forall H, WF_FS None H nil
                              
  | T_FS_NA : forall H F FS sigma,
                WF_Frame H (ann_frame F ann_epsilon) sigma ->
                WF_FS None H FS ->
                WF_FS None H ((ann_frame F ann_epsilon) :: FS)
                      
  | T_FS_NA2 : forall H F FS sigma x tau,
                 ( H , x , tau ## (ann_frame F ann_epsilon) @@ sigma ) ->
                 WF_FS None H FS ->
                 WF_FS (Some (x, tau)) H ((ann_frame F ann_epsilon) :: FS)
                       
  | T_FS_A : forall H F FS x tau ,
                WF_Frame H (ann_frame F (ann_var x)) tau ->
                WF_FS (Some (x, tau)) H FS ->
                WF_FS None H ((ann_frame F (ann_var x)) :: FS)

  | T_FS_A2 : forall H F FS y sigma x tau,
                ( H, y, sigma ## (ann_frame F (ann_var x)) @@ tau) ->
                WF_FS (Some (x, tau)) H FS ->
                WF_FS (Some (y, sigma)) H ((ann_frame F (ann_var x)) :: FS).
  
  
  (* Notation "[ ! H , x , tau ## FS ]" := (WF_FS (Some (x, tau)) H FS) (at level 0). *)
  (* Notation "[ ! H ## FS ]" := (WF_FS None H FS) (at level 0). *)
  
End WF_Env.