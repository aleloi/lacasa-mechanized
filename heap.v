(* Require Import syntax. *)
(* Require Import partial. *)
Require Import namesAndTypes.

Import ConcreteEverything.


Definition fieldMap (rto: RTObject) : FM_type :=
  match rto with
    | obj _ FM => FM
  end.

Import Coq.Lists.List.

Definition fmPointsInside (H: Heap_type) (fm: FM_type) : Prop :=
  forall f0: FieldName_type,
  forall o: Ref_type,
    p_FM.func fm f0 = Some (FM_ref o) ->
    In o (p_heap.domain H).

Definition allPointInside (H: Heap_type) : Prop :=
  forall o: Ref_type,
  forall rto: RTObject,
    p_heap.func H o = Some rto ->
    fmPointsInside H (fieldMap rto).
