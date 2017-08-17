Require Import Init.

Load Types.

(** ある述語を満たす集合が一つのみであること *)
Definition unique (p : SET -> Prop) := (exists x, p x) /\ (forall x y, p x /\ p y -> x = y).

Lemma exists_and_Unique (p : SET -> Prop) : unique p <-> exists! x, p x.
Proof.
 split.
 -
  intros pUnique.
  case pUnique.
  intros pExists pForall.
  case pExists.
  intros x px.
  exists x.
  split.
  +
   apply px.
  +
   intros x' px'.
   apply pForall.
   split.
   *
    apply px.
   *
    apply px'.
 -
  intros pExists.
  case pExists.
  intros x pUnique.
  case pUnique.
  intros px pForall.
  split.
  +
   exists x.
   apply px.
  +
   intros y y' pyy'.
   case pyy'.
   intros py py'.
   replace y with x.
   *
    apply pForall.
    apply py'.
   *
    apply pForall.
    apply py.
Qed.

(** Pを満たして一意に存在する集合 *)
Axiom unique_set : forall (P : SET -> Prop), unique P -> SET.
(** Uniquedの性質の公理 *)
Axiom UniqueAx : forall (P : SET -> Prop) (U : unique P), P (unique_set P U).