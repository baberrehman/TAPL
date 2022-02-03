(*
Chapter 11
*)

Require Import TLC.LibLN.

Inductive typ : Set :=
  | t_arrow : typ -> typ -> typ
  | t_bool  : typ
  | t_unit  : typ
  | t_list  : typ -> typ.

Inductive exp : Set :=
  | e_fvar : var -> exp
  | e_bvar : nat -> exp
  | e_abs : typ -> exp -> exp
  | e_app : exp -> exp -> exp
  | e_tru : exp
  | e_fls : exp
  | e_cond : exp -> exp -> exp -> exp
  | e_unit : exp (* unit *)
  | e_asc  : exp -> typ -> exp (* Ascription *)
  | e_let  : exp -> exp -> exp (* Let *)
  | e_nil : typ -> exp (* nil list *)
  | e_cons : typ -> exp -> exp -> exp (* cons list *)
  | e_isnil : typ -> exp -> exp (* nil check list *)
  | e_head : typ -> exp -> exp (* head list *)
  | e_tail : typ -> exp -> exp. (* tail list *)

Definition env := env typ.

Fixpoint subst_ee (x : var) (s t: exp) {struct t} : exp :=
  match t with
  | e_fvar y => If (y = x) then s else e_fvar y
  | e_bvar i => e_bvar i
  | e_abs T t1 => e_abs T (subst_ee x s t1)
  | e_app t1 t2 => e_app (subst_ee x s t1) (subst_ee x s t2)
  | e_tru => e_tru
  | e_fls => e_fls
  | e_cond t t1 t2 => e_cond (subst_ee x s t) (subst_ee x s t1) (subst_ee x s t2)
  | e_unit => e_unit
  | e_asc e T => e_asc (subst_ee x s e) T
  | e_let e1 e2 => e_let (subst_ee x s e1) (subst_ee x s e2)
  | e_nil T => e_nil T
  | e_cons T h t => e_cons T (subst_ee x s h) (subst_ee x s t)
  | e_isnil T e => e_isnil T (subst_ee x s e)
  | e_head T e => e_head T (subst_ee x s e)
  | e_tail T e => e_tail T (subst_ee x s e)
end.

Fixpoint open_ee_rec (j : nat) (s t: exp) {struct t} : exp :=
  match t with
  | e_fvar y => e_fvar y
  | e_bvar i => If (i = j) then s else e_bvar i
  | e_abs T t1 => e_abs T (open_ee_rec (S j) s t1)
  | e_app t1 t2 => e_app (open_ee_rec j s t1) (open_ee_rec j s t2)
  | e_tru => e_tru
  | e_fls => e_fls
  | e_cond t t1 t2 => e_cond (open_ee_rec j s t) (open_ee_rec j s t1) (open_ee_rec j s t2)
  | e_unit => e_unit
  | e_asc e T => e_asc (open_ee_rec j s e) T
  | e_let e1 e2 => e_let (open_ee_rec j s e1) (open_ee_rec (S j) s e2)
  | e_nil T => e_nil T
  | e_cons T h t => e_cons T (open_ee_rec j s h) (open_ee_rec j s t)
  | e_isnil T e => e_isnil T (open_ee_rec j s e)
  | e_head T e => e_head T (open_ee_rec j s e)
  | e_tail T e => e_tail T (open_ee_rec j s e)
end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

Inductive lc_exp : exp -> Prop :=
  | lc_fvar : forall x,
      lc_exp (e_fvar x)
  | lc_abs : forall (L:vars) (e:exp) T,
      (forall x , x \notin L -> lc_exp (open_ee e (e_fvar x)))  ->
     lc_exp (e_abs T e)
  | lc_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     lc_exp (e_app e1 e2)
  | lc_tru : 
      lc_exp e_tru
  | lc_fls : 
      lc_exp e_fls
  | lc_cond : forall e e1 e2,
      lc_exp e ->
      lc_exp e1 ->
      lc_exp e2 ->
      lc_exp (e_cond e e1 e2)
  | lc_unit :
      lc_exp e_unit
  | lc_asc : forall e T,
      lc_exp e ->
      lc_exp (e_asc e T)
  | lc_let : forall (L:vars) e1 e2,
      lc_exp e1 ->
      (forall x , x \notin L -> lc_exp (open_ee e2 (e_fvar x))) ->
      lc_exp (e_let e1 e2)
  | lc_nil : forall T,
      lc_exp (e_nil T)
  | lc_cons : forall T h t,
      lc_exp h ->
      lc_exp t ->
      lc_exp (e_cons T h t)
  | lc_isnil: forall T e,
      lc_exp e ->
      lc_exp (e_isnil T e)
  | lc_head : forall T e,
      lc_exp e ->
      lc_exp (e_head T e)
  | lc_tail : forall T e,
      lc_exp e ->
      lc_exp (e_tail T e).


Inductive value : exp -> Prop :=
  | val_abs : forall T e,
      value (e_abs T e)
  | val_tru : 
      value e_tru
  | val_fls : 
      value e_fls
  | val_unit : 
      value e_unit
  | val_nil : forall T,
      value (e_nil T)
  | val_cons : forall T h t,
      value h ->
      value t ->
      value (e_cons T h t).


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
  | typ_tru : forall E,
      ok E ->
      typing E e_tru t_bool
  | typ_fls : forall E,
      ok E ->
      typing E e_fls t_bool
  | typ_cond : forall E e e1 e2 T,
      typing E e t_bool ->
      typing E e1 T ->
      typing E e2 T ->
      typing E (e_cond e e1 e2) T
  | typ_unit : forall E,
      ok E ->
      typing E e_unit t_unit
  | typ_asc : forall E e T,
      typing E e T ->
      typing E (e_asc e T) T
  | typ_let : forall (L:vars) E e1 e2 T1 T2,
      typing E e1 T1 ->
           (forall x, x \notin L -> 
        typing (E & x ~ T1) (open_ee e2 (e_fvar x)) T2) ->
      typing E (e_let e1 e2) T2
  | typ_nil : forall E T,
      ok E ->
      typing E (e_nil T) (t_list T)
  | typ_cons : forall T E h t,
      typing E h T ->
      typing E t (t_list T) ->
      typing E (e_cons T h t) (t_list T)
  | typ_isnil: forall E T e,
      typing E e (t_list T) ->
      typing E (e_isnil T e) t_bool
  | typ_head : forall E T e,
      typing E e (t_list T) ->
      typing E (e_head T e) T
  | typ_tail : forall E T e,
      typing E e (t_list T) ->
      typing E (e_tail T e) (t_list T).


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
     step (e_app (e_abs T e) v) (open_ee e v)
 | step_cond : forall e e1 e2 e',
     lc_exp e1 ->
     lc_exp e2 ->
     step e e' ->
     step (e_cond e e1 e2) (e_cond e' e1 e2)
 | step_condl : forall e1 e2,
     lc_exp e1 ->
     lc_exp e2 ->
     step (e_cond e_tru e1 e2) e1
 | step_condr : forall e1 e2,
     lc_exp e1 ->
     lc_exp e2 ->
     step (e_cond e_fls e1 e2) e2
 | step_asc : forall e e' T,
     step e e' ->
     step (e_asc e T) (e_asc e' T)
 | step_ascv : forall v T,
     value v ->
     step (e_asc v T) v
 | step_let : forall e1 e2 e1',
     step e1 e1' ->
     step (e_let e1 e2) (e_let e1' e2)
 | step_letv : forall v e2,
     value v ->
     step (e_let v e2) (open_ee e2 v)
  | step_consl : forall T h t h',
      step h h' ->
      step (e_cons T h t) (e_cons T h' t)
  | step_consr : forall T v t t',
      value v ->
      step t t' ->
      step (e_cons T v t) (e_cons T v t')
  | step_isnilnil : forall S T,
      step (e_isnil S (e_nil T)) e_tru
  | step_isnilcons : forall S T v1 v2,
      value v1 ->
      value v2 ->
      step (e_isnil S (e_cons T v1 v2)) e_fls
  | step_isnil : forall T e e',
      step e e' ->
      step (e_isnil T e) (e_isnil T e')
  | step_headcons : forall S T v1 v2,
      value v1 ->
      value v2 ->
      step (e_head S (e_cons T v1 v2)) v1
  | step_head : forall T e e',
      step e e' ->
      step (e_head T e) (e_head T e')
  | step_tailcons : forall S T v1 v2,
      value v1 ->
      value v2 ->
      step (e_tail S (e_cons T v1 v2)) v2
  | step_tail : forall T e e',
      step e e' ->
      step (e_tail T e) (e_tail T e').


Lemma cannonical_form_bool : forall v,
  value v ->
  forall E, typing E v t_bool ->
  v = e_tru \/ v = e_fls.
Proof.
  introv Val Typ.
  inverts Typ; try solve [inverts* Val].
Qed.

Lemma canonical_form_abs : forall v,
  value v ->
  forall T1 T2 E, typing E v (t_arrow T1 T2) ->
  exists e, v = e_abs T1 e.
Proof.
  introv Val Typ. inverts Val; try solve [inverts Typ].
  inverts Typ. exists* e.
Qed.

Lemma cannonical_form_unit : forall v,
  value v ->
  forall E, typing E v t_unit ->
  v = e_unit.
Proof.
  introv Val Typ.
  inverts Typ; try solve [inverts* Val].
Qed.

Lemma cannonical_form_list : forall v,
  value v ->
  forall E T, typing E v (t_list T) ->
  v = e_nil T \/ exists v1 v2, v = e_cons T v1 v2 /\ value v1 /\ value v2.
Proof.
  introv Val Typ.
  inverts Typ; try solve [inverts* Val].
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
  | e_tru => \{}
  | e_fls => \{}
  | e_cond t t1 t2 => (fv_ee t) \u (fv_ee t1) \u (fv_ee t2)
  | e_unit => \{}
  | e_asc e1 T => fv_ee e1
  | e_let e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | e_nil T => \{}
  | e_cons T h t => (fv_ee h) \u (fv_ee t)
  | e_isnil T e => fv_ee e
  | e_head T e => fv_ee e
  | e_tail T e => fv_ee e
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
  (* solve trivial value cases *)
  inductions Typ; try solve [left*].
 - (*case fvar*)
   apply binds_empty_inv in H0. inverts H0.
 - (*case app*)
   right. inverts LC. destruct~ IHTyp1.
   destruct~ IHTyp2.
   apply canonical_form_abs in Typ1; auto.
   destruct Typ1 as [e Typ1].
   subst. exists* (open_ee e e2).
   destruct H0 as [e' H0]. exists*.
   destruct H as [e' H]. exists*.
 - (*case if*)
   right. inverts LC. destruct~ IHTyp1.
   apply cannonical_form_bool in Typ1; auto.
   destruct Typ1. 
   subst. exists*. subst. exists*.
   destruct H as [e' H]. exists*.
 - (*case ascription*)
   inverts LC.
   destruct~ IHTyp.
   right. exists*.
   destruct H as [e' H].
   right. exists*.
 - (*case Let*)
   inverts LC.
   destruct~ IHTyp.
   right. exists*.
   destruct H1 as [e' H1].
   right. exists*.
 - (*case typ_cons*)
   inverts LC.
   destruct~ IHTyp1.
   destruct~ IHTyp2.
   destruct H0 as [e' H0].
   right. exists*.
   destruct H as [e' H].
   right. exists*.
 - (*step typ_isnil*)
   inverts LC.
   destruct~ IHTyp.
   apply cannonical_form_list in Typ; auto.
   destruct Typ.
   subst. right. exists*.
   destruct H1 as [v1 [v2 [H1 [H2 H3]]]].
   subst. right. exists*.
   destruct H as [e' H].
   right. exists*.
 - (*step typ_head*)
   inverts LC.
   destruct~ IHTyp.
   apply cannonical_form_list in Typ; auto.
   destruct Typ. subst.
   admit. (*what is the head of empty list?*)
   destruct H1 as [v1 [v2 [H1 [H2 H3]]]].
   right. subst. exists*.
   destruct H as [e' H].
   right. exists*.
 - (*step typ_tail*)
   inverts LC.
   destruct~ IHTyp.
   apply cannonical_form_list in Typ; auto.
   destruct Typ. subst.
   admit. (*what is the tail of empty list?*)
   destruct H1 as [v1 [v2 [H1 [H2 H3]]]].
   right. subst. exists*.
   destruct H as [e' H].
   right. exists*.
Admitted.

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
  - apply* typ_tru.
  - apply* typ_fls.
  - apply* typ_cond.
  - apply* typ_unit.
  - apply* typ_asc.
  - apply_fresh* typ_let as y.
    forwards*: H0 y E (G & y ~ T1) F.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc in H1.
 - apply* typ_nil.
 - apply* typ_cons.
 - apply* typ_isnil.
 - apply* typ_head.
 - apply* typ_tail.
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
  unfolds open_ee_rec. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_fvar x)).
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
  - split*.
  - split*.
  - split*.
    apply_fresh* lc_let as y.
    forwards*: H0 y.
 - split*.
 - split*.
 - split*.
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
  - (* case beta-reduction *)
    apply_fresh* typ_abs as y.
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
  - apply* typ_tru.
  - apply* typ_fls.
  - apply* typ_cond.
  - apply* typ_unit.
  - apply* typ_asc.
  - (* case Let *)
    apply_fresh* typ_let as y.
    forwards*: H0 y E (F & y ~ T1) x S.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc.
    apply_empty* typing_weakening.
    apply* ok_push.
    forwards*: typing_regular TypS.
    rewrite~ concat_assoc in H1.
    rewrite~ subst_ee_open_ee_var.
    forwards*: typing_regular TypS.
 - apply* typ_nil.
 - apply* typ_cons.
 - apply* typ_isnil.
 - apply* typ_head.
 - apply* typ_tail.
Qed.

Lemma preservation : forall E e T e',
  typing E e T ->
  step e e' ->
  typing E e' T.
Proof.
  introv Typ red.
  gen e'. inductions Typ; intros; try solve [inverts red].
  - (*case typ_app*)
    inverts red.
    eapply typ_app; eauto.
    eapply typ_app; eauto.
    inverts Typ1.
    pick_fresh y.
    forwards*: H7 y.
    rewrite <- (concat_empty_r E).
    rewrite <- (concat_empty_r (E & y ~ T1)) in H.
    rewrite~ (@subst_ee_intro y).
    forwards*: typing_through_subst_ee H.
    rewrite~ (concat_empty_r).
    forwards*: typing_regular Typ2.
  - (*case typ_cond*)
    inverts* red.
    apply* typ_cond.
  - (*case typ_asc*)
    inverts red.
    forwards*: IHTyp H2.
    apply* typ_asc.
    auto.
  - (*case typ_let*)
    inverts red.
    forwards*: IHTyp e1'.
    apply_fresh* typ_let as y.
    pick_fresh y.
    forwards*: H y.
    rewrite <- (concat_empty_r E).
    rewrite <- (concat_empty_r (E & y ~ T1)) in H1.
    rewrite~ (@subst_ee_intro y).
    forwards*: typing_through_subst_ee H1.
    rewrite~ (concat_empty_r).
    forwards*: typing_regular Typ.
  - (*case typ_cons*)
    inverts* red.
    apply* typ_cons.
    apply* typ_cons.
  - (*case typ_isnil*)
    forwards* (OK&LC): typing_regular Typ.
    inverts red.
    apply* typ_tru.
    apply* typ_fls.
    apply* typ_isnil.
  - (*case typ_head*)
    forwards*(OK&LC): typing_regular Typ.
    inverts red.
    inverts* Typ.
    forwards*: IHTyp H2.
    apply* typ_head.
  - (*case typ_tail*)
    forwards*(OK&LC): typing_regular Typ.
    inverts red.
    inverts* Typ.
    forwards*: IHTyp H2.
    apply* typ_tail.
Qed.
