Require Import syntax.
Require Import partial.
Require Import classTable.
(* Require Import Coq.Structures.Equalities. *)


Module Heap (ant: AbstractNamesAndTypes).

  Definition refType := ant.RefM.t.

  (* Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM *)
  (*                      v1 v2 v3 v4. *)
  (* Import syn. *)
  
  Inductive refOrNull :=
  | null : refOrNull
  | ref : refType -> refOrNull.

  Module refOrNullM <: Typ.
    Definition t := refOrNull.
  End refOrNullM.

  Module field_ty <: Typ.
    Definition t := FieldNameM.t.
  End field_ty.

  Module part_FM := Update field_ty refOrNullM v2.
  
  Notation FM_ty := part_FM.PartFunc.

  Inductive RTObject :=
  | obj : ClassNameM.t -> FM_ty -> RTObject.
  Definition fieldMap (rto: RTObject) : FM_ty :=
    match rto with
      | obj _ FM => FM
    end.
  (* mkRTObject { *)
  (*                      rtType : ClassNameM.t; *)
  (*                      fieldMap : FM_ty *)
  (*                    }. *)
  Module rto <: Typ.
    Definition t := RTObject.
  End rto.

  Module part_Heap := Update RefM rto v5.
  Notation Heap_ty := part_Heap.PartFunc.

  Import Coq.Lists.List.

  (* Print part_Heap.PartFunc. *)

  Definition fmPointsInside (H: Heap_ty) (fm: FM_ty) : Prop :=
    forall f0: FieldNameM.t,
      forall o: refType,
        part_FM.func fm f0 = Some (ref o) ->
        In o (part_Heap.domain H).
      
  Definition allPointInside (H: Heap_ty) : Prop :=
    forall o: refType,
    forall rto: RTObject,
      part_Heap.func H o = Some rto ->
        fmPointsInside H (fieldMap rto).

End Heap.
  