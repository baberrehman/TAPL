(*
Chapter 15
Simply Typed Lambda-Calculus with Subtyping

Figure 15-1: Simply Typed Lambda-Calculus with Subtyping
*)

Require Import TLC.LibLN.

Inductive typ : Set :=
  | t_arrow : typ -> typ -> typ
  | t_top  : typ.

Inductive exp : Set :=
  | e_fvar : var -> exp
  | e_bvar : nat -> exp
  | e_abs : typ -> exp -> exp
  | e_app : exp -> exp -> exp.

Inductive value : exp -> Prop :=
  | val_abs : forall T e,
      value (e_abs T e).


Definition env := env typ.

Fixpoint subst_ee (x : var) (s t: exp) {struct t} : exp :=
  match t with
  | e_fvar y => If (y = x) then s else e_fvar y
  | e_bvar i => e_bvar i
  | e_abs T t1 => e_abs T (subst_ee x s t1)
  | e_app t1 t2 => e_app (subst_ee x s t1) (subst_ee x s t2)
end.

Fixpoint open_ee_rec (j : nat) (s t: exp) {struct t} : exp :=
  match t with
  | e_fvar y => e_fvar y
  | e_bvar i => If (i = j) then s else e_bvar i
  | e_abs T t1 => e_abs T (open_ee_rec (S j) s t1)
  | e_app t1 t2 => e_app (open_ee_rec j s t1) (open_ee_rec j s t2)
end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

Inductive lc_exp : exp -> Prop :=
   | lc_fvar : forall x,
        lc_exp (e_fvar x)
   | lc_abs : forall (L:vars) (e:exp) T,
        ( forall x , x \notin L -> lc_exp (open_ee e (e_fvar x)))  ->
       lc_exp (e_abs T e)
   | lc_app : forall (e1 e2:exp),
       lc_exp e1 ->
       lc_exp e2 ->
       lc_exp (e_app e1 e2).

Inductive sub : typ -> typ -> Prop :=
  | s_refl : forall A,
      sub A A
  | s_trans : forall A B C,
      sub A B ->
      sub B C ->
      sub A C
  | s_top : forall A,
      sub A t_top
  | s_arrow : forall A1 A2 B1 B2,
      sub A2 A1 ->
      sub B1 B2 ->
      sub (t_arrow A1 B1) (t_arrow A2 B2).

Inductive typing : env -> exp -> typ -> Prop :=
  | typ_var : forall x E T,
     ok E ->
     binds x T E ->
     typing E (e_fvar x) T
  | typ_abs : forall (L:vars) (E:env) (T1 T2:typ) (e:exp),
     ok E ->
     (forall x, x \notin L -> 
        typing (E & x ~ T1) (open_ee e (e_fvar x)) T2) ->
     typing E (e_abs T1 e) (t_arrow T1 T2)
  | typ_app : forall (E:env) (e1 e2: exp) (T1 T2:typ),
      typing E e1 (t_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (e_app e1 e2) T2
  | typ_sub : forall E T1 e T2,
      typing E e T1 ->
      sub T1 T2 ->
      typing E e T2.

Inductive step : exp -> exp -> Prop :=
  | step_appl : forall e1 e2 e1',
      lc_exp e2 ->
      step e1 e1' ->
      step (e_app e1 e2) (e_app e1' e2)
  | step_appr : forall e1 e2 e2',
      value e1 ->
      step e2 e2' ->
      step (e_app e1 e2) (e_app e1 e2')
 | step_beta : forall (e:exp) (v:exp) T,
     lc_exp (e_abs T e) ->
     value v ->
     step (e_app (e_abs T e) v) (open_ee e v).

#[export]
Hint Constructors sub : core.

Lemma sub_arrow_inv : forall S T1 T2,
  sub S (t_arrow T1 T2) ->
  exists S1 S2, S = (t_arrow S1 S2) /\ sub T1 S1 /\ sub S2 T2.
Proof.
  intros.
  inductions H; eauto.
  forwards*(S1&S2&EQ&sub1&sub2): IHsub2 T1 T2.
  forwards*(S11&S21&EQ1&sub11&sub21): IHsub1 S1 S2.
  exists* S11 S21.
Qed.

Lemma canonical_form_abs : forall v,
  value v ->
  forall T1 T2 E, typing E v (t_arrow T1 T2) ->
  exists e S, v = e_abs S e.
Proof.
  introv Val Typ. inverts Val; try solve [inverts Typ].
  inverts Typ. exists* e T1.
  exists* e T.
Qed.

#[export]
Hint Constructors value step lc_exp step : core.

(** Gathering free names already used in the proofs **)

Fixpoint fv_ee (e:exp) : vars :=
  match e with
  | e_fvar y => \{y}
  | e_bvar i => \{}
  | e_abs T t1 => fv_ee t1
  | e_app t1 t2 => (fv_ee t1) \u (fv_ee t2)
  end.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : exp => fv_ee x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.

Lemma progress : forall e T,
  lc_exp e ->
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof.
  introv LC Typ.
  inductions Typ.
 - apply binds_empty_inv in H0. inverts H0.
 - inverts LC. left*.
 - right. inverts LC. destruct~ IHTyp1.
   destruct~ IHTyp2.
   apply canonical_form_abs in Typ1; auto.
   destruct Typ1 as [e [Typ1]].
   subst. exists* (open_ee e e2).
   destruct H0 as [e' H0]. exists*.
   destruct H as [e' H]. exists*.
 - forwards*: IHTyp.
Qed.

Lemma typing_weakening : forall E F G e T,
  typing (E & G) e T ->
  ok (E & F & G) ->
  typing (E & F & G) e T.
Proof.
  introv Typ Ok. gen F. inductions Typ; simpl; intros.
  - apply* typ_var.
    apply* binds_weaken.
  - apply_fresh* typ_abs as y.
    forwards*: H1 y E (G & y ~ T1) F.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc in H2.
  - apply* typ_app.
  - apply* typ_sub.
Qed.

(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.


Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee_rec. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_ee x u (open_ee t1 t2) =
open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_var*. rewrite* <- open_ee_rec_term.
  case_nat*.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_ee e -> lc_exp u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

Lemma typing_regular : forall E e T,
  typing E e T -> ok E /\ lc_exp e.
Proof.
  introv Typ. inductions Typ; auto.
  - split*.
    apply_fresh lc_abs as y.
    forwards*: H1 y.
  - split*.
Qed.

Lemma typing_through_subst_ee : forall E F x S e T s,
  typing (E & x ~ S & F) e T ->
  typing (E & F) s S ->
  typing (E & F) (subst_ee x s e) T.
Proof.
  introv TypT TypS.
  inductions TypT; simpl.
  - case_var.
    binds_get H0. auto.
    binds_cases H0; apply* typ_var.
  - apply_fresh* typ_abs as y.
    specialize (H1 y).
    forwards*: H1 E (F & y ~ T1) x S.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc.
    apply_empty* typing_weakening.
    (* rewrite <- (concat_empty_r (E & F & y ~ T1)).
    apply* typing_weakening.
    rewrite~ concat_empty_r.
    rewrite~ concat_empty_r. *)
    rewrite~ concat_assoc in H2.
    rewrite~ subst_ee_open_ee_var.
    apply typing_regular in TypS.
    destruct~ TypS.
  - apply* typ_app.
  - apply* typ_sub.
Qed.

Lemma abs_typ_inv_sub : forall E S e T1 T2 A,
  typing E (e_abs S e) A ->
  sub A (t_arrow T1 T2) ->
  exists C2,
    (exists L, forall x, x \notin L -> 
          typing (E & x ~ S) (open_ee e (e_fvar x)) C2)
          /\ sub (t_arrow S C2) (t_arrow T1 T2).
Proof.
  introv Typ Sub. inductions Typ; eauto.
Qed.

Lemma abs_typ_inv1 : forall E S e T1 T2,
  typing E (e_abs S e) (t_arrow T1 T2) ->
  sub T1 S.
Proof.
  introv Typ.
  inductions Typ; eauto.
  apply sub_arrow_inv in H.
  destruct H as [S1 [S2 [EQ [sub1 sub2]]]].
  subst.
  specialize (IHTyp S e S1 S2).
  forwards*: IHTyp.
Qed.


Lemma abs_typ_inv : forall E S e T1 T2,
  typing E (e_abs S e) (t_arrow T1 T2) ->
    (exists L, forall x, x \notin L -> 
          typing (E & x ~ S) (open_ee e (e_fvar x)) T2).
Proof.
  introv Typ. inverts Typ.
  - eauto.
  - forwards*: abs_typ_inv_sub H.
    apply sub_arrow_inv in H0.
    destruct H0 as [S1 [S2 [EQ [sub1 sub2]]]].
    destruct H1 as [C2 [[L TEMP1] sub]].
    subst.
    exists L. intros.
    forwards*: TEMP1 x.
    apply* typ_sub.
Admitted.

Lemma preservation : forall E e T e',
  typing E e T ->
  step e e' ->
  typing E e' T.
Proof.
  introv Typ red.
  gen e'. inductions Typ; intros; try solve [inverts red].
  - inverts red.
    eapply typ_app; eauto.
    eapply typ_app; eauto.
    apply abs_typ_inv in Typ1.
    destruct Typ1 as [[L Typ1] sub].
    pick_fresh y.
    forwards*: Typ1 y.
    rewrite <- (concat_empty_r E).
    rewrite <- (concat_empty_r (E & y ~ T)) in H.
    rewrite~ (@subst_ee_intro y).
    forwards*: typing_through_subst_ee H.
    rewrite~ (concat_empty_r).
    apply* typ_sub.
    forwards*: typing_regular Typ2.
  - forwards*: IHTyp.
    apply* typ_sub.
Qed.
