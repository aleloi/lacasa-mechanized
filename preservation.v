Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import sframe.
Require Import reductions.
Require Import typing.
Require Import Coq.Structures.Equalities.

Module Preservation (VarNameM FieldNameM MethodNameM ClassNameM RefM: Typ)
       (act: AbstractClassTable)
       (v1: Nice VarNameM)
       (v2: Nice FieldNameM)
       (v3: Nice MethodNameM)
       (v4: Nice ClassNameM)
       (v5: Nice RefM).


  Module typ := Typing VarNameM FieldNameM MethodNameM ClassNameM RefM
                       act v1 v2 v3 v4 v5.
  Import typ.

  Module reds := Reductions VarNameM FieldNameM MethodNameM ClassNameM RefM
                           act v1 v2 v3 v4 v5.
  Import reds.

  Module sfr := SFrame VarNameM FieldNameM MethodNameM ClassNameM RefM
                       v1 v2 v3 v4 v5.
  Import sfr.

  
  Theorem preservation_light :
    forall gamma H H' L L' t t' sigma eff,
      Reduction_SF ( reds.sfr.heap_sframe H (reds.sfr.sframe L t))
                   ( reds.sfr.heap_sframe H' (reds.sfr.sframe L' t'))
      ->
      TypeChecks gamma eff t sigma ->
      {sig_gam  | TypeChecks (snd sig_gam) eff t' (fst sig_gam)}.
  
  
  