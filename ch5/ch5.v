
(*

  Chapter 5

*)

Require Import TLC.LibLN.

Inductive trm : Set :=
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm.

Inductive value : trm -> Prop :=
  | val_abs : forall x t,
      value (trm_abs x t).

(*
subst_ee is not capture-avoiding substitution.
It is intentionally kept like this and will be
fixed in later chapters.
*)

Fixpoint subst_ee (x : var) (v t : trm) : trm :=
  match t with
  | trm_var x1    => If (x1 = x) then v else (trm_var x1)
  | trm_abs x1 t1 => trm_abs x1 (subst_ee x v t1)
  | trm_app t1 t2 => trm_app (subst_ee x v t1) (subst_ee x v t2)
  end.

Inductive step : trm -> trm -> Prop :=
  | step_appl : forall t1 t2 t1',
      step t1 t1' ->
      step (trm_app t1 t2) (trm_app t1' t2)
  | step_appr : forall v t2 t2',
      value v ->
      step t2 t2' ->
      step (trm_app v t2) (trm_app v t2')
  | step_abs : forall x t v2,
      value v2 ->
      step (trm_app (trm_abs x t) v2) (subst_ee x v2 t).