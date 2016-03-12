Require Import partial.

Require Import Coq.Structures.Equalities.

Module Type Nice (T: Typ) :=
  (MyDecidableType T) <+ (Infinite T).

Module Type AbstractNamesAndTypes.
  Declare Module VarNameM : Typ.
  Declare Module FieldNameM : Typ.
  Declare Module MethodNameM : Typ.
  Declare Module ClassNameM : Typ.
  Declare Module RefM : Typ.
  Declare Module vn : Nice VarNameM.
  Declare Module fn : Nice FieldNameM.
  Declare Module mn : Nice MethodNameM.
  Declare Module cn : Nice ClassNameM.
  Declare Module rn : Nice RefM.
End AbstractNamesAndTypes.


Module ConcreteNamesAndTypes <: AbstractNamesAndTypes.
  Module VarNameM := natT.
  Module FieldNameM := natT.
  Module MethodNameM := natT.
  Module ClassNameM := natT.
  Module RefM := natT.

  Module natNice <: Nice natT.
    Definition eq_dec := nat_eq_dec.
    Definition constructFresh := infiniteNat.constructFresh.
  End natNice.

  Module vn := natNice.
  Module fn := natNice.
  Module mn := natNice.
  Module cn := natNice.
  Module rn := natNice.
End ConcreteNamesAndTypes.

