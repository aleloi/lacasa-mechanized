Require Import partial.

Require Import Coq.Structures.Equalities.

(* Module Type Nice (T: Typ) := *)
(*   (MyDecidableType T) <+ (Infinite T). *)

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

Module NamesAndTypesAndOtherNames (ant: AbstractNamesAndTypes) .

  Import ant.
       
  Definition VarName_type := ant.VarNameM.t.
  Definition FieldName_type := ant.FieldNameM.t.
  Definition MethodName_type := ant.MethodNameM.t.
  Definition ClassName_type := ant.ClassNameM.t.
  Definition Ref_type := ant.RefM.t.
      

  Inductive FM_Range_type :=
    | FM_null : FM_Range_type
    | FM_ref : Ref_type -> FM_Range_type.

  Module FM_typeM <: Typ .
    Definition t := FM_Range_type.
  End FM_typeM.

  Module p_FM := Update ant.FieldNameM FM_typeM ant.fn.

  Definition FM_type := p_FM.PartFunc.

  (* run-time object *)
  Inductive RTObject :=
  | obj : ClassName_type -> FM_type -> RTObject.

  Module RTObject_typeM <: Typ .
    Definition t := RTObject.
  End RTObject_typeM.

  Module p_heap := Update ant.RefM RTObject_typeM ant.rn.

  Definition Heap_type := p_heap.PartFunc.

  Inductive env_Range_type :=
  | envNull : env_Range_type
  | envRef : Ref_type -> env_Range_type
  | envBox : Ref_type -> env_Range_type.

  Module env_Range_typeM <: Typ.
    Definition t := env_Range_type.
  End env_Range_typeM.

  Module p_env := Update VarNameM env_Range_typeM
                         ant.vn.

  Definition Env_type := p_env.PartFunc.
    
End NamesAndTypesAndOtherNames.
  
  

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

Module ConcreteEverything := NamesAndTypesAndOtherNames ConcreteNamesAndTypes.

