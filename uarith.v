(*
Chapter 3
*)

Require Import TLC.LibLN.


Inductive trm : Set :=
  | tru : trm
  | fals : trm
  | cond : trm -> trm -> trm -> trm.

Inductive value : trm -> Prop :=
  | val_tru  : value tru
  | val_fals : value fals.

Inductive step : trm -> trm -> Prop :=
  | step_iftrue : forall t2 t3,
         step (cond tru t2 t3) t2
  | step_iffals : forall t2 t3,
         step (cond fals t2 t3) t3
  | step_if : forall t1 t1' t2 t3,
         step t1 t1' ->
         step (cond t1 t2 t3) (cond t1' t2 t3).


Lemma determinism : forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
Proof.
  introv red1. gen t2.
  induction red1; intros.
  - inverts H. auto. inverts H4.
  - inverts H. auto. inverts H4.
  - inverts H. inverts red1. inverts red1.
    apply IHred1 in H4. rewrite H4. auto.
Qed.


Definition normal_form (t:trm) := ~ exists t', step t t'.

Lemma value_normal_form : forall v, 
  value v -> normal_form v.
Proof.
  introv Val.
  unfold normal_form.
  unfold not.
  induction Val; intros.
  - destruct H as [t' H]. inverts H.
  - destruct H as [t' H]. inverts H.
Qed.

Lemma normal_form_value : forall v,
   normal_form v -> value v.
Proof.
  induction v; intros.
  apply val_tru.
  apply val_fals.
Admitted.


