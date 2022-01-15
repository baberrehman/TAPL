
(*

chapter 6

*)

Require Import TLC.LibLN.
Require Import TLC.LibNat.


Inductive trm : Set :=
  | trm_var : nat -> trm
  | trm_abs : trm -> trm
  | trm_app : trm -> trm -> trm.

Fixpoint shift (d c : nat) (t : trm) : trm :=
  match t with
  | trm_var k => if (k <? c) then trm_var k else trm_var (k + d)
  | trm_abs t1 => trm_abs (shift d (c+1) t1)
  | trm_app t1 t2 => trm_app (shift d c t1) (shift d c t2)
 end.

Fixpoint subst (j : nat) (s t: trm) : trm :=
  match t with
  | trm_var k => if (k =? j) then s else trm_var k
  | trm_abs t1 => trm_abs (subst (j+1) s t1)
  | trm_app t1 t2 => trm_app (subst j s t1) (subst j s t2)
end.

