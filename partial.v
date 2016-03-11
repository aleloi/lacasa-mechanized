Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.

Module Type Infinite  (Import T: Typ).
                       
  Parameter constructFresh : forall (lT: list t),
                               {fresh: t | ~ In fresh lT}.
End Infinite.

Require Import Coq.Arith.EqNat.
Theorem nat_eq_dec : forall x y : nat, {x=y} + {x <> y}.
  intros.
  set (lem := (eq_nat_decide x y)).
  elim lem.
  intro are_eq.
  left.
  apply (eq_nat_eq x y are_eq).
  intro are_not_eq.
  right.
  intro.
  set (lem2 := proj2 (eq_nat_is_eq x y) H).
  apply (are_not_eq lem2).
Defined.

(* Print UsualDecidableType. *)
    
Module natHasEqDec <: MiniDecidableType.
  Definition t := nat.
  Definition eq_dec := nat_eq_dec.
End natHasEqDec.

(* Print Infinite. *)

(* Print Forall. *)
Require Import Omega.

Lemma maximalNatInd (lN: list nat) (a b: nat):
  Forall (fun x => x < a) lN ->
  Forall (fun x => x < a + b) lN.
  
  induction lN.
  auto.
  intro.
  inversion H.
  apply Forall_cons.
  omega.
  auto.
Qed.  
Lemma maximalNat (lN: list nat) :
  {maxLN | Forall (fun x =>  x < maxLN) lN}.
  
  induction lN.
  exists O.
  apply Forall_nil.
  destruct IHlN.
  exists (x + S a).
  apply Forall_cons.
  omega.
  apply (maximalNatInd lN x (S a) f).
Qed.

    
    (* induction lN. *)
(* apply Forall_nil. *)

Module natT <: Typ.
  Definition t := nat.
End natT.

Module infiniteNat <: Infinite natT.

  Include natT.

  Lemma constructFresh : forall (lT: list t),
                           {fresh: t | ~ In fresh lT}.
    intro.
    set (maxNat := maximalNat lT).
    destruct maxNat.
    exists x.
    induction lT.
    auto.
    intro.
    destruct H.
    inversion f.
    omega.
    inversion f.
    set (lem := IHlT H3).
    destruct H0.
    destruct H1.
    auto.
  Qed.    

End infiniteNat.

(* Lemma fls (A: Set) : False -> A. *)
(*   intro. elim H. *)
(* Defined. *)
(* Print fls. *)

(* Module ConcretePartialFiniteInfiniteDomain <: PartialFiniteInfiniteDomain natEq natHasEqDec. *)
  
(*   Definition B := nat. *)
(*   Definition domain := @nil nat. *)
(*   Definition mapping : forall tVal : nat, In tVal domain -> B. *)
(*     intros. *)
(*     elim H. *)
(*   Defined. *)

  
  
(*   Definition constructFresh := infiniteNat.constructFresh. *)
(* End ConcretePartialFiniteInfiniteDomain. *)

Inductive option (A: Type) :=
| Some : A -> option A
| None : option A.
Arguments Some [A] _.
Arguments None [A].

Theorem not_in_cons_impl (A: Type) (x a : A) (l : list A) :
  ~ In x (a :: l) <-> x <> a /\ ~ In x l.
  split.
  intro.
  split.
  intro.
  apply H.
  destruct H0.
  apply in_eq.
  intro.
  apply H.
  apply (in_cons _ _ _ H0).
  intros.
  destruct H.
  intro.
  apply H0.
  simpl in H1.
  elim H1.
  intro.
  assert False.
  apply H.
  symmetry.
  auto.
  elim H3.
  auto.
Qed.

(* couldn't make sense of UsualDecidableType in the standard library *)
Module Type MyDecidableType (T: Typ).
  Axiom eq_dec: forall x y : T.t, {x=y} + {~x=y}.
End MyDecidableType.

Module Type Nice (T: Typ) :=
  (MyDecidableType T) <+ (Infinite T).

       


Module Update (T BT: Typ) (Import nc: Nice T). 
  Definition B := BT.t.

  Notation A := T.t.

  (* Print nc. *)

  Record PartFunc : Type := mkPartFunc {
                                func: A -> option B;
                                domain: list A;
                                fDomainCompat :
                                  forall valT: A,
                                    ~ In valT domain <-> func valT = None
                              }.

  (*
   * Creates new partial function in which everything in 'dom'
   * has value 'val'.
   *)
  Definition newPartFunc (dom: list A) (val: B) : PartFunc.
    set (func := fun a => match in_dec nc.eq_dec a dom with
                            | left _ => Some val
                            | right _ => None
                          end
        ).
    apply (mkPartFunc func dom).
    intro.
    (* set ( lem := in_dec eq_dec valT dom). *)
    set (funcVal := func valT).
    unfold func in funcVal.
    clear func.
    split.
    intro.
    unfold funcVal.
    elim (in_dec eq_dec valT dom).
    intro.
    elim (H a).
    auto.
    intro.
    unfold funcVal in H.
    (* elim (in_dec eq_dec valT dom). *)
    intro.
    case_eq (in_dec eq_dec valT dom).
    intros.
    rewrite H1 in H.
    inversion H.
    intro.
    elim (n H0).
  Defined.

  Theorem newPartFuncDomain (dom: list A) (val: B) :
    domain (newPartFunc dom val) = dom.
    simpl.
    auto.
  Qed.

  Theorem newPartFuncProp (dom: list A) (val: B) :
    forall a: A,
      (In a dom <-> func (newPartFunc dom val) a = Some val ) /\
      ((~ In a dom) <-> func (newPartFunc dom val) a = None).
    intros.
    simpl.
    split.
    split.
    intro.
    case_eq (in_dec eq_dec a dom).
    intros.
    auto.
    intros.
    contradiction.
    case_eq (in_dec eq_dec a dom).
    intros.
    auto.
    intros.
    discriminate H0.
    split.
    intro.
    case_eq (in_dec eq_dec a dom).
    intros.
    contradiction.
    intros.
    auto.
    intros.
    case_eq (in_dec eq_dec a dom).
    intros.
    rewrite -> H0 in H.
    discriminate.
    intros.
    auto.
  Qed.

  Definition updateFunc (f: A -> option B) (tVal: A) (b: B) :  (A -> option B).
    intro.
    elim (eq_dec X tVal).
    intro.
    exact (Some b).
    intro.
    exact (f X).
  Defined.

  Theorem updateFuncProp (f: A -> option B) (tVal: A) (b: B) :
    forall a: A,
      (a = tVal -> (updateFunc f tVal b) a = Some b) /\
      (a <> tVal -> (updateFunc f tVal b) a = f a).
    intros.
    elim (eq_dec a tVal).
    intro.
    rewrite a0.
    split.
    intro.
    clear H.
    (* Print updateFunc. *)
    compute.
    elim (eq_dec tVal tVal).
    auto.
    intro.
    elim b0. apply eq_refl.
    intro.
    elim H.
    apply eq_refl.
    intro.
    split.
    intro.
    elim b0.
    auto.
    intro.
    compute.
    elim (eq_dec a tVal).
    intro.
    elim H.
    auto.
    intro.
    auto.
  Qed.

  
  Definition updatePartFunc (p: PartFunc) (a: A) (b: B) : PartFunc.
    
    (* destruct (constructFresh (domain p)) as [fresh freshProp]. *)
    set (new_f := updateFunc (func p) a b).
    
    apply (mkPartFunc new_f (cons a (domain p))).
    set (lem := updateFuncProp (func p) a b).
    intro.
    elim (eq_dec valT a).
    intro.
    destruct a0.
    split.
    intro.
    assert False.
    apply H.
    simpl.
    left. auto.
    elim H0.

    set (lemValT := proj1 (lem valT) (eq_refl _)).
    unfold new_f.
    intro.
    assert (None = Some b).
    transitivity (updateFunc (func p) valT b valT).
    auto. auto.
    inversion H0.
    intro.
    set (lemValT := proj2 (lem valT) b0).
    split.
    intro.
    transitivity (func p valT).
    apply (lemValT).
    apply (proj1 (fDomainCompat p valT)).
    intro.
    apply H.
    apply (in_cons _ _ _ H0).
    intro.
    
    set (lem2 := proj2 (not_in_cons_impl _ valT a (domain p))).
    apply lem2.
    split.
    apply b0.
    clear lem2.
    set (compat := proj2 (fDomainCompat p valT)).
    apply compat.
    transitivity (new_f valT).
    symmetry.
    apply lemValT.
    apply H.
  Defined.    
  
  Theorem updatedFuncProp (p: PartFunc) (a: A) (b: B) :
    forall a0: A, 
      (a0 = a -> func (updatePartFunc p a b) a0 = Some b) /\
      ((a0 <> a) -> func (updatePartFunc p a b) a0 = func p a0).
    apply (updateFuncProp (func p) a b).
  Qed.

End Update.

(* Print Update. *)

