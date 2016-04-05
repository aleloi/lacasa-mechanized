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

  Definition method : class -> MethodName_type -> MethDecl -> Prop :=
    fun _ _ _ => classDecls P = nil.

  Definition mtype C m md 
             (witn: method C m md) :=
    retType md.

  Definition mbody C m md
             (witn: method C m md) :=
    methodBody md.

  Definition mparam C m md
             (witn: method C m md) :=
    argName md.

  Definition class_name_methods : class -> list MethDecl :=
    fun _ => match classDecls P with
               | nil => nil
               | _ => nil
             end.

  Definition fld : class -> FieldName_type -> Prop :=
    fun _ _ => classDecls P = nil.

  Definition ftype : forall C f,
                       fld C f -> class :=
    fun C _ _ => C.
  (*   destruct (ant.fn.constructFresh nil). *)
  (*   auto. *)
  (* Defined. *)

  Definition fields : class -> list FieldName_type -> Prop.
  Admitted.

  Definition fieldsList : class -> list FieldName_type.
  Admitted.
  Theorem fieldsListIsFields :
    forall C,
      fields C (fieldsList C).
  Admitted.
    

  Definition subclass : class -> class -> Prop :=
    fun _ _ => classDecls P = nil.

  Theorem subclass_refl C :
    subclass C C.
    admit.
  Admitted.
    
  Theorem subclass_trans C D E:
    subclass C D -> subclass D E -> subclass C E.
    admit.
  Admitted.

  Theorem field_subclass C D f :
    fld D f ->
    subclass C D ->
    fld C f.
    admit.
  Admitted.
    
  Theorem ftype_subclass C D f (f_witn: fld D f)
          (sub_witn: subclass C D):
    ftype D f f_witn = ftype C f (field_subclass C D f f_witn sub_witn).
    admit.
  Admitted.

  Theorem unique_ftype C f (f_witn1 f_witn2: fld C f) :
    ftype C f f_witn1 = ftype C f f_witn2.
    admit.
  Admitted.
    
  Inductive subtype : typecheck_type -> typecheck_type -> Prop :=
  | classSub : forall C D, subclass C D -> subtype (typt_class C) (typt_class D)
  | boxSub : forall C D, subclass C D -> subtype (typt_box C) (typt_box D)
  | allSub : forall sigma, subtype sigma typt_all.

  Definition ocap : class -> Prop.
  Admitted.

  Theorem ocap_dec : forall C, ocap C \/ ~ (ocap C).
  Admitted.

  Fixpoint lookup_l (c: class) (l: list ClassDecl) : option ClassDecl :=
    match l with
      | nil => None
      | cd :: cds => if class_eq_dec c (cls cd)
                     then (Some cd)
                     else (lookup_l c cds)
    end.

  Definition lookup (c: class) : option ClassDecl :=
    lookup_l c (classDecls P).

End MethodsAndFields.

