Require Import Init.

Require Import Types.

(** ある条件を満たしただ一つ存在する集合の省略法。Coq.Logic.Descriptionに似た公理がある。 *)

(** pを満たす値がただ一つのみ存在すること。Uniqueness quantificationより命名。 *)
Definition uniquant (A : Type) (p : A -> Prop)
 := (exists x, p x) /\ (forall x y, p x -> p y -> x = y).

(** SETのuniquant *)
Definition set_uniquant := uniquant SET.

(** uniquantと既存の構文との関係 *)
Theorem uniquant_existence (A : Type) (p : A -> Prop)
 : uniquant A p <-> exists! x, p x.
Proof.
 apply unique_existence.
Qed.

(** Pを満たして一意に存在する集合 *)
Axiom UniqueSet : forall (p : SET -> Prop), set_uniquant p -> SET.
(** Uniquedの性質の公理 *)
Axiom UniqueAx : forall (p : SET -> Prop) (h : set_uniquant p), p (UniqueSet p h).

(** ただ一つのみ存在するということから集合の記述を得る。 *)
Theorem set_description (p : SET -> Prop) : set_uniquant p -> { x : SET | p x }.
Proof.
 intros pUni.
 exists (UniqueSet p pUni).
 apply UniqueAx.
Qed.