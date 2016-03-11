Require Import partial.

Require Import Coq.Structures.Equalities.

Module Type Nice (T: Typ) :=
  (MyDecidableType T) <+ (Infinite T).

Module Type AbstractNamesAndTypes (VarNameM FieldNameM MethodNameM ClassNameM : Typ)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM).
End AbstractNamesAndTypes.

Print AbstractNamesAndTypes.
Module 
