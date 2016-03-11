Require Import syntax.
Require Import partial.
Require Import Coq.Structures.Equalities.

Module Type AbstractClassTable (VarNameM FieldNameM MethodNameM ClassNameM: Typ)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM).

  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                       v1 v2 v3 v4.

  Parameter CT: list syn.ClassDecl.
End AbstractClassTable.

Module ConcreteClassTable  (VarNameM FieldNameM MethodNameM ClassNameM: Typ)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)  <:
  AbstractClassTable VarNameM FieldNameM MethodNameM
                     ClassNameM v1 v2 v3 v4.
  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                       v1 v2 v3 v4.
  Definition CT := @nil syn.ClassDecl.
End ConcreteClassTable.  

Module ClassTable (VarNameM FieldNameM MethodNameM ClassNameM: Typ)
       (act: AbstractClassTable)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM).

  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                       v1 v2 v3 v4.
  Import syn.

  (* Parameter CT : list ClassDecl. *)
  (* Maybe change to method name? *)
  Definition method : ClassName -> MethDecl -> Prop :=
    fun _ _ => False.

  Definition methods : ClassName -> list MethDecl :=
    fun _ => nil. 
  
  Definition fld : ClassName -> FieldName -> Prop :=
    fun _ _ => False.
  
  Definition fields : ClassName -> list FieldName -> Prop :=
    fun _ _ => False.

End ClassTable.



  