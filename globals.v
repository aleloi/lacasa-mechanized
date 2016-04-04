Require Import syntax.
Require Import partial.
Require Import namesAndTypes.
Require Import heap.
Require Import classTable.
Require Import wf_env.


Import ConcreteEverything.

Section Globals.
  Variable P : Program.

  Require Import Coq.Lists.List.

  Print sig.

  Definition global_heap_lst (lst: varDefs) : (* Heap_type * *)Gamma_type * Env_type.
    induction lst.
    exact ((* p_heap.emptyPartFunc,  *)p_gamma.emptyPartFunc, p_env.emptyPartFunc).
    destruct IHlst.
    (* destruct p. *)
    destruct a.
    rename c into C.
    (* rename h into H. *)
    rename e into L.
    rename p into Gamma.
    (* set (o_fresh := ConcreteNamesAndTypes.vn.constructFresh (p_heap.domain H)). *)
    (* destruct o_fresh as [o  o_fresh_proof]. *)
        
    (* set (flds := fieldsList P C). *)
    (* set (FM := p_FM.newPartFunc flds FM_null). *)
    (* set (heapVal := obj C FM). *)
    split.
    (* split. *)
    (* exact (p_heap.updatePartFunc H o heapVal ). *)
    exact (p_gamma.updatePartFunc Gamma v (typt_class C)).
    exact (p_env.updatePartFunc L v envNull).
  Defined.

  Definition globalEnv (P: Program) : (* Heap_type *  *)Gamma_type * Env_type  :=
    global_heap_lst (globals P).

  (* Theorem WF_globals: *)
  (*   let (p, L) := globalEnv P in let (H, Gamma) := p in WF_Env P H Gamma L. *)
  (*   destruct P. *)
  (*   set (P' := {| *)
  (*    classDecls := classDecls; *)
  (*    globals := globals; *)
  (*    programBody := programBody; *)
  (*    programBodyIsTerm := programBodyIsTerm |}). *)
  (*   unfold globalEnv. *)
  (*   induction (syntax.globals P'). *)
  (*   simpl. *)
  (*   split. *)
  (*   intro. *)
  (*   intro. *)
  (*   simpl in H. *)
  (*   elim H. *)
  (*   intros. *)
  (*   simpl in H.     *)
  (*   simplify_eq H. *)

  (*   case_eq (global_heap_lst v). *)
  (*   intros. *)
  (*   destruct p. *)
  (*   rename H into hyp. *)
  (*   rename h into H; rename p into Gamma; rename e into L. *)
  (*   simpl. *)
  (*   rewrite hyp. *)
  (*   destruct a. *)
  (*   rename c into C. *)
  (*   rename v0 into x. *)
  (*   rename v into rest. *)
  (*   case_eq (ConcreteNamesAndTypes.vn.constructFresh (p_heap.domain H)). *)
  (*   intros o o_fresh. *)
  (*   intro dummy; clear dummy. *)

  (*   split. *)
  (*   rewrite hyp in IHv. *)
  (*   destruct IHv. *)
  (*   apply subset_preserved. *)
  (*   assumption. *)


    
    
End Globals.