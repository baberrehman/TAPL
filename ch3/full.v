(*
Chapter 3
*)

Require Import TLC.LibLN.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
Require Import Coq.Init.Nat.


Inductive trm : Set :=
  | tru : trm
  | fals : trm
  | cond : trm -> trm -> trm -> trm
  | zro  : trm
  | succ : trm -> trm
  | pred : trm -> trm
  | iszero : trm -> trm.

Lemma eq_dec : forall x y:trm, {x = y} + {x <> y}.
Proof.
 decide equality; auto.
Defined.

Notation "l1 `union` l2" := (set_union eq_dec l1 l2) (at level 80).
Notation "l1 `inter` l2" := (set_inter eq_dec l1 l2) (at level 80).

Fixpoint constants (u: trm) : list trm := 
  match u with
  | tru => [tru]
  | fals => [fals]
  | cond t1 t2 t3 => constants t1 `union` constants t2 `union` constants t3
  | zro => [zro]
  | succ t => constants t
  | pred t => constants t
  | iszero t => constants t
  end.

Fixpoint size (u: trm) : nat := 
  match u with
  | tru => 1
  | fals => 1
  | cond t1 t2 t3 => 1 + size t1 + size t2 + size t3
  | zro => 1
  | succ t => 1 + size t
  | pred t => 1 + size t
  | iszero t => 1 + size t
  end.

Fixpoint depth (u: trm) : nat := 
  match u with
  | tru => 1
  | fals => 1
  | cond t1 t2 t3 => max (max (depth t1) (depth t2)) (depth t3) + 1
  | zro => 1
  | succ t => 1 + depth t
  | pred t => 1 + depth t
  | iszero t => 1 + depth t
  end.
