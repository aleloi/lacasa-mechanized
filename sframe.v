Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import namesAndTypes.
Import ConcreteEverything.


Inductive sframe_type := | sframe : Env_type -> ExprOrTerm -> sframe_type.
Inductive sfconfig_type := | sfconfig :  Heap_type -> sframe_type -> sfconfig_type.
Notation "( # H , L , t ! )" := (sfconfig H (sframe L t)) (at level 0).

(* Alternatives:
 *  1. Change language to allow exprs, not terms in sframe. Add reduction rules. Modify progress theorem conclusion.
 *
 *  2. Add isTerm here
 *  3. Add isTerm somewhere in well-formedness
 *  4. Don't do anything here, but do not add extra reduction rules. Modify progress theorem conclusion (slightly).
 * 
 *)

