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
  Definition v_eq_dec := ant.vn.eq_dec.
  Definition fn_eq_dec := ant.vn.eq_dec.
  Definition mn_eq_dec := ant.mn.eq_dec.
  Definition cn_eq_dec := ant.cn.eq_dec.
  Definition rn_eq_dec := ant.rn.eq_dec.

  Definition var_name_this :=
    let fresh := vn.constructFresh nil in let (x, _) := fresh in x.
  
  Inductive annotation_type :=
  | ann_epsilon : annotation_type
  | ann_var : VarName_type -> annotation_type.
  
  Inductive class :=
  | AnyRef : class
  | extends : ClassName_type -> class -> class.

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
  | obj : class -> FM_type -> RTObject.

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

  
  Theorem class_eq_dec : forall x y : class, {x = y } + {x <> y}.
    intro.
    induction x.
    intro.
    destruct y.
    left; reflexivity.
    right; simplify_eq.

    intro y'.
    destruct y'.
    right; simplify_eq.
    set (ind_hyp := IHx y').
    destruct ind_hyp.
    rewrite e.
    destruct (cn_eq_dec c c0).
    rewrite e0.
    left; reflexivity.
    right.
    intro H; inversion H.
    firstorder.

    right; intro H; inversion H.
    firstorder.
  Qed.
        

  Inductive typecheck_type :=
  | typt_class : class -> typecheck_type
  | typt_box : class -> typecheck_type
  | typt_all : typecheck_type.

  Inductive effect :=
  | eff_ocap : effect
  | eff_epsilon : effect.

  Module tyM <: Typ.
    Definition t := typecheck_type.
  End tyM.

  Module p_gamma := Update VarNameM tyM vn.

  Notation Gamma_type := p_gamma.PartFunc.

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

