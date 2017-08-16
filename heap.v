Require Import syntax.
(* Require Import partial. *)
Require Import namesAndTypes.
Require Import classTable.

Import ConcreteEverything.

Section Heap.
  Variable P: Program.
  Definition fieldsP := fields P.
  Definition subclassP := subclass P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  

  Definition fieldMap (rto: RTObject) : FM_type :=
    match rto with
      | obj _ FM => FM
    end.

  Import Coq.Lists.List.

  Check p_heap.in_part_func_domain_conv.
  
  Definition heap_typeof (H: Heap_type) (o: Ref_type)
             (witn: In o (p_heap.domain H)) :
    class.
    set (value := (p_heap.in_part_func_domain_conv H o witn) ).
    destruct value.
    destruct x.
    exact c.
  Defined.

  Print heap_typeof.

  Theorem heap_typeof_same (H: Heap_type) (o: Ref_type) C FM :
    p_heap.func H o = Some (obj C FM) ->
    forall witn,
      heap_typeof H o witn = C.
    intros.
    unfold heap_typeof.
    destruct (p_heap.in_part_func_domain_conv H o witn).
    generalize e.
    rewrite H0.
    intro.

    inversion e0.
    rewrite <- H2 in *.
    
    clear P H o H0 witn e.
    (* Aww, this is unfair! It's almost done now!*)
    (* replace x with  (obj C FM) by apply proof_irrelevance. 
     *)
  Admitted.

  Theorem heap_typeof_impl H o C :
    forall witn,
      heap_typeof H o witn = C ->
      {FM | p_heap.func H o = Some (obj C FM)}.
    intros.
    case_eq (p_heap.func H o).
    intros.
    destruct b.
    rewrite (heap_typeof_same H o c f H1 witn) in H0.
    rewrite H0 in *; clear H0 c.
    exists f; reflexivity.

    (* None *)
    intro is_none; induction (proj2 (p_heap.fDomainCompat _ _) is_none witn).
  Qed.    
    

  Hint Resolve heap_typeof_same : Hints.
  Hint Resolve heap_typeof_impl : Hints.

  Definition Heap_obj_ok H C FM :=
    forall f o,
    forall f_witn : fldP C f, 
      p_FM.func FM f = Some (FM_ref o) ->
      { o_witn: In o (p_heap.domain H) &
                subclassP (heap_typeof H o o_witn)
                          (ftypeP C f f_witn)
      }.

  Definition Heap_dom_ok H : Prop :=
    forall (o: p_heap.A) C FM,
      p_heap.func H o = Some (obj C FM) ->
      fieldsP C (p_FM.domain FM).

  Definition Heap_ok H : Prop :=
    forall (o: p_heap.A) C FM,
      p_heap.func H o = Some (obj C FM) ->
      Heap_obj_ok H C FM.

End Heap.
