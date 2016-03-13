Require Import syntax.
Require Import partial.
Require Import namesAndTypes.

Import ConcreteEverything.

Section MethodsAndFields.
  Variable P : Program.

  Require Import Coq.Lists.List.
  
(* Module MethodsAndFields (ct: ClassTable). *)

  (* Parameter CT : list ClassDecl. *)
  (* Maybe change to method name? *)

  Definition method : ClassName_type -> MethDecl -> Prop :=
    fun _ _ => classDecls P = nil.

  Definition methods : ClassName_type -> list MethDecl :=
    fun _ => match classDecls P with
               | nil => nil
               | _ => nil
             end.

  Definition fld : ClassName_type -> FieldName_type -> Prop :=
    fun _ _ => classDecls P = nil.

  Definition ftype : forall C f,
                       fld C f -> ClassName_type :=
    fun C _ _ => C.
  (*   destruct (ant.fn.constructFresh nil). *)
  (*   auto. *)
  (* Defined. *)

  Definition fields : ClassName_type -> list FieldName_type -> Prop :=
    fun _ _ => classDecls P = nil.

  Definition subclass : ClassName_type -> ClassName_type -> Prop :=
    fun _ _ => classDecls P = nil.

  Inductive subtype : typecheck_type -> typecheck_type -> Prop :=
  | classSub : forall C D, subclass C D -> subtype (typt_class C) (typt_class D)
  | boxSub : forall C D, subclass C D -> subtype (typt_box C) (typt_box D)
  | allSub : forall sigma, subtype sigma typt_all.

End MethodsAndFields.

