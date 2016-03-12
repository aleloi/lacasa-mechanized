Require Import syntax.
Require Import partial.
Require Import namesAndTypes.
Require Import Coq.Structures.Equalities.

Module Type AbstractClassTable (ant: AbstractNamesAndTypes).

  Module syn := Syntax ant.

  Parameter CT: list syn.ClassDecl.
End AbstractClassTable.

Module ConcreteClassTable  (ant: AbstractNamesAndTypes).
  Module syn := Syntax ant.
  Definition CT := @nil syn.ClassDecl.
End ConcreteClassTable.  

Module ClassTable (ant: AbstractNamesAndTypes) (act: AbstractClassTable ant).

  
  Import act.syn.

  (* Parameter CT : list ClassDecl. *)
  (* Maybe change to method name? *)
  Definition method : ClassName -> MethDecl -> Prop :=
    fun _ _ => False.

  Definition methods : ClassName -> list MethDecl :=
    fun _ => nil. 
  
  Definition fld : ClassName -> FieldName -> Prop :=
    fun _ _ => False.

  Definition ftype : forall C f,
                       fld C f -> ClassName.
    destruct (ant.fn.constructFresh nil).
    auto.
  Defined.
  
  Definition fields : ClassName -> list FieldName -> Prop :=
    fun _ _ => False.

  Definition subclass : ClassName -> ClassName -> Prop :=
    fun _ _ => False.

End ClassTable.



  