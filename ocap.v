Require Import syntax.
Require Import partial.
Require Import namesAndTypes.
Require Import classTable.

Import ConcreteEverything.

Section Ocap.
  Variable P : Program.

  Require Import Coq.Lists.List.

  (* Everything should be initialized to null... TODO: refactor*)
  Definition global_env_lst (lst: varDefs) : Env_type.
    induction lst.
    exact p_env.emptyPartFunc.
    destruct a.
    rename IHlst into L.
    exact (p_env.updatePartFunc L v envNull).
  Defined.

  Definition globalEnv : Env_type :=
    global_env_lst (globals P).

  
  Fixpoint noGlobalsExpr (env : list VarName_type) (e: Expr) : Prop :=
    match e with 
      | Null => True
      | Var x => In x env
      | FieldSelection x _ => In x env
      | FieldAssignment x _ y => In x env /\ In y env
      | MethodInvocation x _ z => In x env /\ In z env
      | New _ => True
      | Box _ => True
      | Open x y t' => (In x env) /\ noGlobalsTerm (y :: env) t'
    end
  with 
  noGlobalsTerm (env : list VarName_type) (t: Term) : Prop :=
    match t with 
      | TVar x => In x env
      | TLet x e t' => noGlobalsExpr env e /\ noGlobalsTerm (x :: env) t'
    end.
  
  Definition methodNoGlobals (md: MethDecl) : Prop :=
    noGlobalsTerm (var_name_this :: argName md :: nil) (methodBody md).

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

  
  Fixpoint directlyRelatedTerm (t: Term) A :=
    match t with
      | TLet _ e t' => directlyRelatedExpr e A \/ directlyRelatedTerm t' A
      | _ => False
    end
  with
  directlyRelatedExpr (e: Expr) A :=
    match e with
      | New A' => A' = A
      | Box A' => A' = A
      | Open _ _ t' => directlyRelatedTerm t' A
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

