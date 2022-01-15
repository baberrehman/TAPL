(*
Chapter 3
*)

Require Import TLC.LibLN.

Inductive trm : Set :=
  | tru  : trm
  | fls  : trm
  | cond : trm -> trm -> trm -> trm
  | O    : trm
  | succ : trm -> trm
  | pred : trm -> trm
  | iszero : trm -> trm.

Inductive value : trm -> Prop :=
  | val_tru : value tru
  | val_fls : value fls
  | val_zro : value O
  | val_succ : forall v, value v -> value (succ v).

Inductive step : trm -> trm -> Prop :=
  | step_tru : forall t2 t3,
         step (cond tru t2 t3) t2
  | step_fls : forall t2 t3,
         step (cond fls t2 t3) t3
  | step_if : forall t1 t1' t2 t3,
         step t1 t1' ->
         step (cond t1 t2 t3) (cond t1' t2 t3) 
  | step_succ : forall t1 t1',
         step t1 t1' ->
         step (succ t1) (succ t1')
  | step_pred_O :
         step (pred O) O
  | step_pred_succ : forall t,
         value t ->
         step (pred (succ t)) t
  | step_pred : forall t t',
         step t t' ->
         step (pred t) (pred t')
  | step_iszerozero : 
         step (iszero O) tru
  | step_iszerosucc : forall v,
         value v ->
         step (iszero (succ v)) fls
  | step_iszero : forall t1 t1',
         step t1 t1' ->
         step (iszero t1) (iszero t1').

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
  - destruct H as [t' H]. inverts H.
  - destruct H as [t' H]. inverts H.
    apply IHVal. exists* t1'.
Qed.

Lemma normal_form_value : forall v,
   ~ normal_form v -> ~ value v.
Proof.
  induction v; unfold not; intros;
  try solve [apply value_normal_form in H0;
  contradiction].
Qed.

Lemma determinism : forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
Proof.
  introv red1. gen t2.
  induction red1; introv red2.
  - inverts red2. auto. inverts H3.
  - inverts red2. auto. inverts H3.
  - inverts red2. inverts red1. inverts red1.
    forwards*: IHred1 H3. subst. auto.
  - inverts red2.
    apply IHred1 in H0. rewrite H0. auto.
  - inverts red2. auto. inverts H0.
  - invert red2; intros. auto. subst.
    inverts H1.
    apply value_normal_form in H.
    unfold normal_form in H.
    false. apply H. exists* t1'.
  - inverts red2. inverts red1.
    inverts red1.
    apply value_normal_form in H0.
    unfold normal_form in H0.
    false. apply H0. exists* t1'.
    forwards: IHred1 H0. subst. auto.
  - inverts red2. auto. inverts H0.
  - inverts red2. auto.
    inverts H1.
    apply value_normal_form in H.
    unfold normal_form in H.
    false. apply H. exists* t1'0.
  - inverts red2. inverts red1.
    inverts red1.
    apply value_normal_form in H0.
    unfold normal_form in H0.
    false. apply H0. exists* t1'0.
    forwards*: IHred1 H0.
    subst~.
Qed.

Inductive stepm : trm -> trm -> Prop :=
  | step_single : forall t t',
      step t t' -> 
      stepm t t'
  | step_refl : forall t,
      stepm t t
  | step_trans : forall t t' t'',
      stepm t t' ->
      stepm t' t'' ->
      stepm t t''.

Lemma determinism_multi : forall t t1 t2,
  value t1 ->
  value t2 ->
  stepm t t1 -> stepm t t2 -> t1 = t2.
Proof.
  introv val1 val2 red1 red2.
  induction red1. 
 - gen t'. induction red2; intros.
  apply* (@determinism t).
  apply value_normal_form in val2.
  unfold normal_form in val2.
  false. apply val2. exists* t'.
  forwards*: IHred2_2 val2 val1.
  
  apply value_normal_form in val1.
  unfold normal_form in val1.
  false. apply val1.
Admitted.