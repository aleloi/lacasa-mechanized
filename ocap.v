Require Import syntax.
Require Import partial.
Require Import namesAndTypes.
Require Import classTable.

Import ConcreteEverything.

Section Ocap.
  Variable P : Program.

  Require Import Coq.Lists.List.

  Print sig.

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

  
  