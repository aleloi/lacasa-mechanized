Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import Coq.Structures.Equalities.

Module Reductions (VarNameM FieldNameM MethodNameM ClassNameM RefM: Typ)
       (act: AbstractClassTable)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)
       (v5: Nice RefM).

  Module syn := Syntax VarNameM FieldNameM MethodNameM ClassNameM
                        v1 v2 v3 v4.
  Module hip := Heap FieldNameM ClassNameM RefM
                     v2 v5.

  Module sfr := SFrame VarNameM FieldNameM MethodNameM ClassNameM RefM
                       v1 v2 v3 v4 v5.
  Import sfr.

  Module ct := ClassTable VarNameM FieldNameM MethodNameM ClassNameM
                          act v1 v2 v3 v4.

  Import syn.
  Import sfr.
  Import hip.
  Notation "( p +++ a --> b )" := (part_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o --> obj )" := (part_Heap.updatePartFunc
                                              H o obj)
                                      (at level 0).
  Notation heapUpd := part_Heap.updatePartFunc.

  (* Notation "$$ C FM $$" := (obj C FM) (at level 201). *)

  (* let x = y in t*)
  Import Coq.Lists.List.
  

  Definition fm2env : refOrNull -> sfr.envRangeTy :=
    fun (a: refOrNull) =>
      match a with
        | null => sfr.envNull
        | ref o => sfr.ref o
      end.

  Definition is_not_box (a: sfr.envRangeTy) : Prop :=
    match a with
      | sfr.envNull => True
      | sfr.ref _ => True
      | sfr.box _ => False
    end.

  Definition env2fm (envVal: sfr.envRangeTy) (witn: is_not_box envVal)
  : refOrNull.
    case_eq envVal.
    intro.
    apply null.
    intros.
    apply (ref r).
    intros.
    unfold is_not_box in witn.
    rewrite -> H in witn.
    contradiction.
  Defined.
  
  
  Inductive Reduction_SF :
    sf_config -> sf_config -> Prop :=
  | E_Var : forall x y t H L null_ref_box,
              syn.isTerm t -> 
              part_env.func L y = Some null_ref_box ->
              Reduction_SF ( # H , L , t_let x <- (Var y) t_in t ! )
                        ( # H , (L +++ x --> null_ref_box) , t !)

  | E_Null : forall x t H L,
              syn.isTerm t -> 
              Reduction_SF ( # H , L , t_let x <- Null t_in t ! )
                        ( # H , (L +++ x --> envNull) , t !)

  | E_New : forall C o x t H L FM flds,
              syn.isTerm t ->
              ~ In o (part_Heap.domain H) ->
              ct.fields C flds ->
              FM = hip.part_FM.newPartFunc flds null ->
              Reduction_SF ( # H , L , t_let x <- New C t_in t ! )
                        ( # (H +*+ o --> (obj C FM)),
                          ( L +++ x --> sfr.ref o ) , t ! )

  | E_Box : forall C o x t H L FM flds,
              syn.isTerm t ->
              ~ In o (part_Heap.domain H) ->
              ct.fields C flds ->
              FM = hip.part_FM.newPartFunc flds null ->
              Reduction_SF ( # H , L , t_let x <- Box C t_in t ! )
                        ( # (H +*+ o --> (obj C FM)),
                          ( L +++ x --> sfr.box o ) , t ! )

  | E_Field : forall x y o f t H L C FM fmVal,
                syn.isTerm t ->
                part_env.func L y = Some (sfr.ref o) ->
                part_Heap.func H o = Some (obj C FM) ->
                part_FM.func FM f = Some fmVal ->
                Reduction_SF ( # H , L , t_let x <- (FieldSelection y f) t_in t ! )
                        ( # H,
                          ( L +++ x --> (fm2env fmVal) ) , t ! )

  (* 
   * Added is_not_box envVal to E_Assign, because range of
   * FM would have to change otherwise.
   *)
  | E_Assign : forall x y z o f t H L C FM envVal,
                 forall witn: is_not_box envVal, 
                   syn.isTerm t ->
                   part_env.func L y = Some (sfr.ref o) ->
                   part_Heap.func H o = Some (obj C FM) ->
                   In f (part_FM.domain FM) ->
                   part_env.func L z = Some envVal ->
                   Reduction_SF ( # H , L , t_let x <- (FieldAssignment y f z) t_in t ! )
                             ( # (H +*+ o --> (obj C (part_FM.updatePartFunc
                                                       FM f (env2fm envVal witn)
                                                    )
                                             )),
                               ( L +++ x --> envVal) , t ! ).


  Inductive Annotation :=
  | ann_epsilon : Annotation
  | ann_var : VarType -> Annotation.
  
  Notation ann_F_ty := (prod sframe_ty Annotation).
     
  Notation FS_ty := (list ann_F_ty).

  Notation cfg_ty := (prod Heap_ty FS_ty).

  

  Definition updFrame (F: ann_F_ty) (x: VarType) (envVal: sfr.envRangeTy) :
    ann_F_ty.
    destruct F.
    destruct s.
    exact (sframe ( p +++ x --> envVal ) e, a).
  Defined.

  Inductive Reduction_FS : cfg_ty -> cfg_ty -> Prop :=

  | E_StackFrame : forall H H' L L' t t' FS a,
                    Reduction_SF ( # H , L , t ! ) ( # H' , L' , t' ! )  ->
                    Reduction_FS (H, ((sframe L t, a) :: FS) )
                                 (H', (sframe L' t', a) :: FS )

  | E_Return1 : forall H L x y F FS envVal,
                  part_env.func L x = Some envVal ->
                  Reduction_FS (H, ((sframe L (Var x), ann_var y) :: F :: FS))
                               (H, updFrame F y envVal :: FS)

  | E_Return2 : forall H F FS,
                  Reduction_FS (H, (F, ann_epsilon) :: FS)
                               (H, FS)
                               
  | E_Open : forall H L x1 x2 y t1 t2 ann FS o,
               isTerm t1 ->
               isTerm t2 ->
               part_env.func L x2 = Some (sfr.box o) ->
               In o (part_Heap.domain H) ->
               Reduction_FS (H, (sframe L
                                        ( t_let x1 <- (Open x2 y t1) t_in t2 ),
                                 ann) :: FS)
                            (H, (sframe (part_env.emptyPartFunc +++ y --> (sfr.box o) )  t1, ann_epsilon)
                                  :: (sframe ( L +++ x1 --> (sfr.box o) ) t2,
                                      ann) :: FS).
  (* TODO: E_invoke *)
                            
End Reductions.
