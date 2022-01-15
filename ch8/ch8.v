(*
Chapter 8
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

Inductive typ : Set :=
  | typ_bool : typ
  | typ_nat  : typ.

Inductive typing : trm -> typ -> Prop :=
  | t_tru : typing tru typ_bool
  | t_fls : typing fls typ_bool
  | t_cond : forall t1 t2 t3 T,
       typing t1 typ_bool ->
       typing t2 T ->
       typing t3 T ->
       typing (cond t1 t2 t3) T
  | t_O : typing O typ_nat
  | t_succ : forall t1,
       typing t1 typ_nat ->
       typing (succ t1) typ_nat
  | t_pred : forall t1,
       typing t1 typ_nat ->
       typing (pred t1) typ_nat
  | t_iszero : forall t1,
       typing t1 typ_nat ->
       typing (iszero t1) typ_bool.

(*
Inversion Lemmas
*)

Lemma one : forall T, typing tru T -> T = typ_bool.
Proof.
  intros. inverts* H.
Qed.

Lemma two : forall T, typing fls T -> T = typ_bool.
Proof.
  intros. inverts* H.
Qed.

Lemma three : forall t1 t2 t3 T,
  typing (cond t1 t2 t3) T ->
  typing t1 typ_bool /\ typing t2 T /\ typing t3 T.
Proof.
  intros. inverts* H.
Qed.

Lemma typ_unique : forall t T1 T2,
  typing t T1 ->
  typing t T2 ->
  T1 = T2.
Proof.
  induction 1; intros; try solve [inverts* H].
  inverts* H2.
  inverts* H0.
  inverts* H0.
  inverts* H0.
Qed.

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

Lemma canonical_forms_bool : forall v,
  value v ->
  typing v typ_bool ->
  v = tru \/ v = fls.
Proof.
  induction 1; intros; auto.
  inverts H. inverts H0.
Qed.

Lemma canonical_forms_nat : forall v,
  value v ->
  typing v typ_nat ->
  v = O \/ exists v', v = (succ v').
Proof.
  induction 1; intros; auto.
  inverts H. inverts H.
  inverts H0.
  forwards*: IHvalue H2.
Qed.

Hint Constructors value typing step.

Lemma progress : forall t T,
  typing t T ->
  value t \/ exists t', step t t'.
Proof.
  induction 1; try solve [left*].
  right. destruct IHtyping1.
  inverts* H. inverts H2. inverts H2.
  destruct H2 as [t'].
  exists* (cond t' t2 t3).
  destruct~ IHtyping.
  destruct H0 as [t'].
  right. exists* (succ t').
  destruct IHtyping.
  apply canonical_forms_nat in H; auto.
  destruct~ H. subst.
  right. exists* O.
  right. destruct H as [v']. subst~.
  inverts H0. exists* v'.
  destruct H0 as [t'].
  right. exists* (pred t').
  right. destruct IHtyping.
  apply canonical_forms_nat in H; auto.
  destruct H. subst. exists* tru.
  destruct H as [v']. subst.
  inverts H0. exists* fls.
  destruct H0 as [t'].
  exists*.
Qed.


Lemma preservation : forall t T t',
  typing t T ->
  step t t' ->
  typing t' T.
Proof.
  introv Typ Red. gen t'.
  induction Typ; intros; try solve [inverts Red].
  inverts* Red.
  inverts* Red.
  inverts* Red. inverts* Typ.
  inverts* Red.
Qed.
