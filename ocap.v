Require Import syntax.
Require Import partial.
Require Import namesAndTypes.
Require Import classTable.

Import ConcreteEverything.

Section Ocap.
  Variable P : Program.

  Require Import Coq.Lists.List.

    
  (* Everything should be initialized to null... TODO: refactor*)
  Definition global_heap_lst (lst: varDefs) : Heap_type * Env_type.
    induction lst.
    exact (p_heap.emptyPartFunc, p_env.emptyPartFunc).
    destruct IHlst.
    set (o_fresh := ConcreteNamesAndTypes.vn.constructFresh (p_heap.domain h)).
    destruct o_fresh as [o  o_fresh_proof].
    destruct a.
    rename c into C.
    rename h into H.
    rename e into L.
    set (flds := fieldsList P C).
    set (FM := p_FM.newPartFunc flds FM_null).
    set (heapVal := obj C FM).
    split.
    exact (p_heap.updatePartFunc H o heapVal ).

    exact (p_env.updatePartFunc L v (envRef o)).
  Defined.

  Definition globalHeap (P: Program) : Heap_type * Env_type:=
    global_heap_lst (globals P).

  Fixpoint noGlobals (env : list VarName_type) (t: ExprOrTerm) : Prop :=
    match t with
      | Null => True
      | Var x => In x env
      | FieldSelection x _ => In x env
      | FieldAssignment x _ y => In x env /\ In y env
      | MethodInvocation x _ z => In x env /\ In z env
      | New _ => True
      | Box _ => True

      | Open x y t' => In x env /\ noGlobals (y :: env) t'
      | TLet x e t' => noGlobals env e /\ noGlobals (x :: env) t'
    end.
  
  Definition methodNoGlobals (md: MethDecl) : Prop :=
    noGlobals (var_name_this :: argName md :: nil) (methodBody md).

  Definition classDeclNoGlobals (cd: ClassDecl) : Prop :=
    Forall methodNoGlobals (methods cd).

  Inductive directlyNotOcap (C: class) : Prop :=
  | directlyNotOcapConstr :
      forall cd,
        lookup P C = Some cd ->
        ~ classDeclNoGlobals cd ->
        directlyNotOcap C.

  Fixpoint directlyRelatedFieldlst (fs: flds) (A: class) :=
    match fs with
      | nil => False
      | (_, A') :: fs' => A = A' \/ directlyRelatedFieldlst fs' A
    end.

  Definition directlyRelatedField (cd: ClassDecl) A := directlyRelatedFieldlst
                                                         (cdFields cd) A.

  
  Definition directlyRelatedTerm (t: ExprOrTerm) (A: class) :=
    match t with
      | New A' => A = A'
      | _ => False
    end.

  Definition directlyRelatedMethod (md: MethDecl) A :=
    argType md = typt_class A \/
    directlyRelatedTerm (methodBody md) A.

  
  Inductive directlyRelated : class -> class -> Prop :=
  | directlyRelatedByInheritance :
      forall C_name B,
        directlyRelated (extends C_name B) B

  | directlyRelatedByMethod :
      forall A cdA B,
        lookup P A = Some cdA ->
        Exists (fun md => directlyRelatedMethod md B)
               (methods cdA) ->
        directlyRelated A B

  | directlyRelatedByField :
      forall A cdA B,
        directlyRelatedField cdA B ->
        directlyRelated A B.

  Require Import Coq.Relations.Relation_Operators.

  Definition indirectlyRelated := clos_refl_trans_1n _ directlyRelated.

  Inductive notOcap : class -> Prop :=
  | notOcapConstr :
      forall A B,
        directlyNotOcap B ->
        indirectlyRelated A B ->
        notOcap A.

  Definition ocap (C: class):  Prop :=
    ~ notOcap C.
    
  
End Ocap.

