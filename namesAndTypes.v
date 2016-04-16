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
  Definition fn_eq_dec := ant.fn.eq_dec.
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

  Module VarNameM.
    Inductive _var_name_type :=
    | _var_name_type_constr : nat -> _var_name_type.
    Definition t := _var_name_type.
  End VarNameM.

  Module FieldNameM.
    Inductive _field_name_type :=
    | _field_name_type_constr : nat -> _field_name_type.
    Definition t := _field_name_type.
  End FieldNameM.

  Module MethodNameM.
    Inductive _method_name_type :=
    | _method_name_type_constr : nat -> _method_name_type.
    Definition t := _method_name_type.
  End MethodNameM.

  Module ClassNameM.
    Inductive _class_name_type :=
    | _class_name_type_constr : nat -> _class_name_type.
    Definition t := _class_name_type.
  End ClassNameM.

  Module RefM.
    Inductive _ref_type :=
    | _ref_type_constr : nat -> _ref_type.
    Definition t := _ref_type.
  End RefM.

  

  Module varNameNice <: Nice VarNameM.
    Import VarNameM.
    Lemma _var_name_eq_dec :
      forall (x y : _var_name_type),
        {x = y} + {x <> y}.
      intros.
      destruct x as [nx]; destruct y as [ny].
      case_eq (nat_eq_dec nx ny); intros; clear H.
      left; rewrite e; reflexivity.
      right; simplify_eq; assumption.
    Qed.
    Definition eq_dec := _var_name_eq_dec.
    

    Require Import Coq.Lists.List.

    Lemma _var_name_type_constructFresh
     : forall lT : list _var_name_type,
         {fresh : _var_name_type | ~ In fresh lT}.
      Definition unpack (x: _var_name_type) :=
        match x with | _var_name_type_constr nx => nx end.
      intros.
      set (lTn := map unpack lT).
      destruct (infiniteNat.constructFresh lTn) as [fresh_nat fresh_nat_is_fresh].

      
      assert (forall x1 x2, unpack x1 = unpack x2 -> x1 = x2) as unpack_injective.
      intros.
      destruct x1 as [n1]; destruct x2 as [n2].
      simplify_eq H; intro are_eq; rewrite are_eq; reflexivity.
      
      set (lem := count_occ_map unpack _var_name_eq_dec nat_eq_dec unpack_injective
                                (_var_name_type_constr fresh_nat) lT
          ).
      fold lTn in lem.
      simpl in lem.
      set (lemlem := proj1 (count_occ_not_In nat_eq_dec lTn fresh_nat) fresh_nat_is_fresh).
      rewrite lemlem in lem.
      set (lemlemlem := proj2 (count_occ_not_In _var_name_eq_dec lT (_var_name_type_constr fresh_nat))
                              lem).
      exact (exist _ (_var_name_type_constr fresh_nat) lemlemlem).
    Qed.
      
    Definition constructFresh := _var_name_type_constructFresh.
  End varNameNice.

  Module fieldNameNice <: Nice FieldNameM.
    Import FieldNameM.
    Lemma _field_name_eq_dec :
      forall (x y : _field_name_type),
        {x = y} + {x <> y}.
      intros.
      destruct x as [nx]; destruct y as [ny].
      case_eq (nat_eq_dec nx ny); intros; clear H.
      left; rewrite e; reflexivity.
      right; simplify_eq; assumption.
    Qed.
    Definition eq_dec := _field_name_eq_dec.
    

    Require Import Coq.Lists.List.

    Lemma _field_name_type_constructFresh
     : forall lT : list _field_name_type,
         {fresh : _field_name_type | ~ In fresh lT}.
      Definition unpack (x: _field_name_type) :=
        match x with | _field_name_type_constr nx => nx end.
      intros.
      set (lTn := map unpack lT).
      destruct (infiniteNat.constructFresh lTn) as [fresh_nat fresh_nat_is_fresh].

      
      assert (forall x1 x2, unpack x1 = unpack x2 -> x1 = x2) as unpack_injective.
      intros.
      destruct x1 as [n1]; destruct x2 as [n2].
      simplify_eq H; intro are_eq; rewrite are_eq; reflexivity.
      
      set (lem := count_occ_map unpack _field_name_eq_dec nat_eq_dec unpack_injective
                                (_field_name_type_constr fresh_nat) lT
          ).
      fold lTn in lem.
      simpl in lem.
      set (lemlem := proj1 (count_occ_not_In nat_eq_dec lTn fresh_nat) fresh_nat_is_fresh).
      rewrite lemlem in lem.
      set (lemlemlem := proj2 (count_occ_not_In _field_name_eq_dec lT (_field_name_type_constr fresh_nat))
                              lem).
      exact (exist _ (_field_name_type_constr fresh_nat) lemlemlem).
    Qed.
      
    Definition constructFresh := _field_name_type_constructFresh.
  End fieldNameNice.

  Module methodNameNice <: Nice MethodNameM.
    Import MethodNameM.
    Lemma _method_name_eq_dec :
      forall (x y : _method_name_type),
        {x = y} + {x <> y}.
      intros.
      destruct x as [nx]; destruct y as [ny].
      case_eq (nat_eq_dec nx ny); intros; clear H.
      left; rewrite e; reflexivity.
      right; simplify_eq; assumption.
    Qed.
    Definition eq_dec := _method_name_eq_dec.
    

    Require Import Coq.Lists.List.

    Lemma _method_name_type_constructFresh
     : forall lT : list _method_name_type,
         {fresh : _method_name_type | ~ In fresh lT}.
      Definition unpack (x: _method_name_type) :=
        match x with | _method_name_type_constr nx => nx end.
      intros.
      set (lTn := map unpack lT).
      destruct (infiniteNat.constructFresh lTn) as [fresh_nat fresh_nat_is_fresh].

      
      assert (forall x1 x2, unpack x1 = unpack x2 -> x1 = x2) as unpack_injective.
      intros.
      destruct x1 as [n1]; destruct x2 as [n2].
      simplify_eq H; intro are_eq; rewrite are_eq; reflexivity.
      
      set (lem := count_occ_map unpack _method_name_eq_dec nat_eq_dec unpack_injective
                                (_method_name_type_constr fresh_nat) lT
          ).
      fold lTn in lem.
      simpl in lem.
      set (lemlem := proj1 (count_occ_not_In nat_eq_dec lTn fresh_nat) fresh_nat_is_fresh).
      rewrite lemlem in lem.
      set (lemlemlem := proj2 (count_occ_not_In _method_name_eq_dec lT (_method_name_type_constr fresh_nat))
                              lem).
      exact (exist _ (_method_name_type_constr fresh_nat) lemlemlem).
    Qed.
      
    Definition constructFresh := _method_name_type_constructFresh.
  End methodNameNice.

  Module classNameNice <: Nice ClassNameM.
    Import ClassNameM.
    Lemma _class_name_eq_dec :
      forall (x y : _class_name_type),
        {x = y} + {x <> y}.
      intros.
      destruct x as [nx]; destruct y as [ny].
      case_eq (nat_eq_dec nx ny); intros; clear H.
      left; rewrite e; reflexivity.
      right; simplify_eq; assumption.
    Qed.
    Definition eq_dec := _class_name_eq_dec.
    

    Require Import Coq.Lists.List.

    Lemma _class_name_type_constructFresh
     : forall lT : list _class_name_type,
         {fresh : _class_name_type | ~ In fresh lT}.
      Definition unpack (x: _class_name_type) :=
        match x with | _class_name_type_constr nx => nx end.
      intros.
      set (lTn := map unpack lT).
      destruct (infiniteNat.constructFresh lTn) as [fresh_nat fresh_nat_is_fresh].

      
      assert (forall x1 x2, unpack x1 = unpack x2 -> x1 = x2) as unpack_injective.
      intros.
      destruct x1 as [n1]; destruct x2 as [n2].
      simplify_eq H; intro are_eq; rewrite are_eq; reflexivity.
      
      set (lem := count_occ_map unpack _class_name_eq_dec nat_eq_dec unpack_injective
                                (_class_name_type_constr fresh_nat) lT
          ).
      fold lTn in lem.
      simpl in lem.
      set (lemlem := proj1 (count_occ_not_In nat_eq_dec lTn fresh_nat) fresh_nat_is_fresh).
      rewrite lemlem in lem.
      set (lemlemlem := proj2 (count_occ_not_In _class_name_eq_dec lT (_class_name_type_constr fresh_nat))
                              lem).
      exact (exist _ (_class_name_type_constr fresh_nat) lemlemlem).
    Qed.
      
    Definition constructFresh := _class_name_type_constructFresh.
  End classNameNice.

  Module refNice <: Nice RefM.
    Import RefM.
    Lemma _ref_eq_dec :
      forall (x y : _ref_type),
        {x = y} + {x <> y}.
      intros.
      destruct x as [nx]; destruct y as [ny].
      case_eq (nat_eq_dec nx ny); intros; clear H.
      left; rewrite e; reflexivity.
      right; simplify_eq; assumption.
    Qed.
    Definition eq_dec := _ref_eq_dec.
    
    Require Import Coq.Lists.List.

    Lemma _ref_type_constructFresh
     : forall lT : list _ref_type,
         {fresh : _ref_type | ~ In fresh lT}.
      Definition unpack (x: _ref_type) :=
        match x with | _ref_type_constr nx => nx end.
      intros.
      set (lTn := map unpack lT).
      destruct (infiniteNat.constructFresh lTn) as [fresh_nat fresh_nat_is_fresh].

      
      assert (forall x1 x2, unpack x1 = unpack x2 -> x1 = x2) as unpack_injective.
      intros.
      destruct x1 as [n1]; destruct x2 as [n2].
      simplify_eq H; intro are_eq; rewrite are_eq; reflexivity.
      
      set (lem := count_occ_map unpack _ref_eq_dec nat_eq_dec unpack_injective
                                (_ref_type_constr fresh_nat) lT
          ).
      fold lTn in lem.
      simpl in lem.
      set (lemlem := proj1 (count_occ_not_In nat_eq_dec lTn fresh_nat) fresh_nat_is_fresh).
      rewrite lemlem in lem.
      set (lemlemlem := proj2 (count_occ_not_In _ref_eq_dec lT (_ref_type_constr fresh_nat))
                              lem).
      exact (exist _ (_ref_type_constr fresh_nat) lemlemlem).
    Qed.
      
    Definition constructFresh := _ref_type_constructFresh.
  End refNice.

  Module vn := varNameNice.
  Module fn := fieldNameNice.
  Module mn := methodNameNice.
  Module rn := refNice.
  Module cn := classNameNice.
  
End ConcreteNamesAndTypes.

Module ConcreteEverything := NamesAndTypesAndOtherNames ConcreteNamesAndTypes.

