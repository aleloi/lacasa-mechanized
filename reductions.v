Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import namesAndTypes.
Require Import ocap.

Import ConcreteEverything.

Section Reductions.
  Variable P : Program.

  Notation "( p +++ a --> b )" := (p_env.updatePartFunc
                                     p a b) (at level 0).

  Notation "( H +*+ o --> obj )" := (p_heap.updatePartFunc
                                              H o obj)
                                      (at level 0).
  Notation heapUpd := p_heap.updatePartFunc.

  Notation fieldsP := (fields P).

  (* Notation "$$ C FM $$" := (obj C FM) (at level 201). *)

  (* let x = y in t*)
  Import Coq.Lists.List.
  

  Definition fm2env : FM_Range_type -> env_Range_type :=
    fun (a: FM_Range_type) =>
      match a with
        | FM_null => envNull
        | FM_ref o => envRef o
      end.

  Definition is_not_box (a: env_Range_type) : Prop :=
    match a with
      | envNull => True
      | envRef _ => True
      | envBox _ => False
    end.

  Definition env2fm (envVal: env_Range_type) (witn: is_not_box envVal)
  : FM_Range_type.
    case_eq envVal.
    intro.
    apply FM_null.
    intros.
    apply (FM_ref r).
    intros.
    unfold is_not_box in witn.
    rewrite -> H in witn.
    contradiction.
  Defined.

    
  Inductive Reduction_SF :
    sfconfig_type -> sfconfig_type -> Type :=
  | E_Var : forall x y t H L null_ref_box,
              p_env.func L y = Some null_ref_box ->
              Reduction_SF ( # H , L , t_let x <- (Var y) t_in t ! )
                        ( # H , (L +++ x --> null_ref_box) , t ! ) 

  | E_Null : forall x t H L,
               Reduction_SF ( # H , L , t_let x <- Null t_in t ! )
                        ( # H , (L +++ x --> envNull) , t !)

  | E_New : forall C o x t H L FM flds,
              ~ In o (p_heap.domain H) ->
              fieldsP C flds ->
              FM = p_FM.newPartFunc flds FM_null ->
              Reduction_SF ( # H , L , t_let x <- New C t_in t ! )
                        ( # (H +*+ o --> (obj C FM)),
                          ( L +++ x --> envRef o ) , t ! )

  | E_Box : forall C o x t H L FM flds,
              ~ In o (p_heap.domain H) ->
              fieldsP C flds ->
              FM = p_FM.newPartFunc flds FM_null ->
              Reduction_SF ( # H , L , t_let x <- Box C t_in t ! )
                        ( # (H +*+ o --> (obj C FM)),
                          ( L +++ x --> envBox o ) , t ! )

  | E_Field : forall x y o f t H L C FM fmVal,
                p_env.func L y = Some (envRef o) ->
                p_heap.func H o = Some (obj C FM) ->
                p_FM.func FM f = Some fmVal ->
                Reduction_SF ( # H , L , t_let x <- (FieldSelection y f) t_in t ! )
                        ( # H,
                          ( L +++ x --> (fm2env fmVal) ) , t ! )
  

  (* 
   * Added is_not_box envVal to E_Assign, because range of
   * FM would have to change otherwise.
   *)
  | E_Assign : forall x y z o f t H L C FM envVal,
                 forall witn: is_not_box envVal, 
                   p_env.func L y = Some (envRef o) ->
                   p_heap.func H o = Some (obj C FM) ->
                   In f (p_FM.domain FM) ->
                   p_env.func L z = Some envVal ->
                   Reduction_SF ( # H , L , t_let x <- (FieldAssignment y f z) t_in t ! )
                             ( # (H +*+ o --> (obj C (p_FM.updatePartFunc
                                                       FM f (env2fm envVal witn)
                                                    )
                                             )),
                               ( L +++ x --> envVal) , t ! ).

  Inductive ann_frame_type :=
  | ann_frame : sframe_type -> annotation_type -> ann_frame_type.


       
  Notation FS_type := (list ann_frame_type).

  Notation cfg_type := (prod Heap_type FS_type).

  Definition updFrame (F: ann_frame_type) (x: VarName_type) (envVal: env_Range_type) :
    ann_frame_type.
    destruct F.
    destruct s.
    exact ( ann_frame (sframe ( e +++ x --> envVal ) t) a).
  Defined.
  
  Inductive Reduction_FS : cfg_type -> cfg_type -> Type:=

  | E_StackFrame : forall H H' L L' t t' FS a,
                    Reduction_SF ( # H , L , t ! ) ( # H' , L' , t' ! )  ->
                    Reduction_FS (H, ( (ann_frame (sframe L t)  a) :: FS) )
                                 (H', (ann_frame (sframe L' t') a) :: FS )

  | E_Return1 : forall H L x y F FS envVal,
                  p_env.func L x = Some envVal ->
                  Reduction_FS (H, (ann_frame (sframe L (TVar x)) (ann_var y)) :: F :: FS)
                               (H, updFrame F y envVal :: FS)

  | E_Return2 : forall H L x FS,
                  Reduction_FS (H, (ann_frame (sframe L (TVar x)) ann_epsilon) :: FS)
                               (H, FS)
                               
  | E_Open : forall H L x1 x2 y t1 t2 ann FS o,
               p_env.func L x2 = Some (envBox o) ->
               In o (p_heap.domain H) ->
               Reduction_FS (H, (ann_frame (sframe L
                                        ( t_let x1 <- (Open x2 y t1) t_in t2 ))
                                 ann) :: FS)
                            (H, (ann_frame (sframe (p_env.emptyPartFunc +++ y --> (envBox o) )  t1)
                                           ann_epsilon)
                                  :: (ann_frame (sframe ( L +++ x1 --> (envBox o) ) t2)
                                                ann) :: FS)

  (* x <- y.m(z) in t 
   *  L(y) = o
   *  H(o) = <C, FM>
   *  mbody(C, m) = t'
   *  mparam(C, m) = p
   *  L0 = globals
   *)
  | E_Invoke : forall H t' t L L' x y z p m l o C FM FS md Lz,
                 forall (witn: method P C m md), 
                   p_env.func L y = Some (envRef o) ->   (* L y = o*)
                   p_env.func L z = Some Lz ->           (* z in dom(L) *)
                   p_heap.func H o = Some (obj C FM) ->  (* H o = <C, FM> *)
                   mbody P C m md witn = t' ->           (* mbody(C, m) = t' *)
                   mparam P C m md witn = p ->           (* mparam(C, m) = p *)
                   L' =                        (* L' = L[this -> o, p -> L z]*)
                   p_env.updatePartFunc
                     (p_env.updatePartFunc
                        (globalEnv P)
                        var_name_this (envRef o))
                     p Lz
                   ->
                   Reduction_FS
                     (H,
                      (ann_frame
                         (sframe L
                          t_let x <- MethodInvocation y m z t_in t) l)
                        :: FS)
                     (H, (ann_frame (sframe L' t') (ann_var x))
                           ::
                           (ann_frame (sframe L t) l)
                           ::
                           FS
                     ).
  
End Reductions.
