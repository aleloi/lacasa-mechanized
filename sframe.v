Require Import syntax.
Require Import partial.
Require Import heap.
Require Import classTable.
Require Import namesAndTypes.
Import ConcreteEverything.


Inductive sframe_type := | sframe : Env_type -> Term -> sframe_type.
Inductive sfconfig_type := | sfconfig :  Heap_type -> sframe_type -> sfconfig_type.
Notation "( # H , L , t ! )" := (sfconfig H (sframe L t)) (at level 0).
