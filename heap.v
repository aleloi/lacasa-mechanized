Require Import syntax.
(* Require Import partial. *)
Require Import namesAndTypes.
Require Import classTable.

Import ConcreteEverything.

Section Heap.
  Variable P: Program.
  Definition fieldsP := fields.
  Definition subclassP := subclass P.
  Definition fldP := fld P.
  Definition ftypeP := ftype P.
  

  Definition fieldMap (rto: RTObject) : FM_type :=
    match rto with
      | obj _ FM => FM
    end.

  Import Coq.Lists.List.

  Definition heap_typeof (H: Heap_type) (o: Ref_type)
             (witn: In o (p_heap.domain H)) :
    class.
    set (lem := proj2 (p_heap.fDomainCompat H o)).
    case_eq (p_heap.func H o).
    intros;    destruct b;    exact c.
    intro is_none; set (is_absurd := lem is_none); firstorder.
  Defined.


  (* Definition heap_type H o (o_witn: In o (p_heap.domain H)) : ClassName_type. *)
  (*   set (lem := proj2 (p_heap.fDomainCompat H o)). *)
  (*   case_eq (p_heap.func H o). *)
  (*   intros. *)
  (*   destruct b. *)
  (*   exact c. *)
  (*   intro is_none; elim ((lem is_none) o_witn). *)
  (* Defined. *)

  Definition Heap_obj_ok H C FM :=
    forall f o,
    forall f_witn : fldP C f, 
      p_FM.func FM f = Some (FM_ref o) ->
      { o_witn: In o (p_heap.domain H) &
                subclassP (heap_typeof H o o_witn)
                          (ftypeP C f f_witn)
      }.

  Definition Heap_dom_ok H : Prop :=
    forall o C FM,
      p_heap.func H o = Some (obj C FM) ->
      fieldsP C (p_FM.domain FM).

  Definition Heap_ok H : Prop :=
    forall o C FM,
      p_heap.func H o = Some (obj C FM) ->
      Heap_obj_ok H C FM.

End Heap.
