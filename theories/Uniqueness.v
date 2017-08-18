Require Import Init.

Require Import Types.

(** ある条件を満たしただ一つ存在する集合の省略法。Coq.Logic.Descriptionに似た公理がある。 *)

(** pを満たす値がただ一つのみ存在すること。Uniqueness quantificationより命名。 *)
Definition uniquant {A : Type} (p : A -> Prop)
 := (exists x, p x) /\ (forall x y, p x -> p y -> x = y).

Theorem uniquant_existence (A : Type) (p : A -> Prop)
 : uniquant p <-> exists! x, p x.
Proof.
 apply unique_existence.
Qed.

(** Pを満たして一意に存在する集合 *)
Axiom UniqueSet : forall (p : SET -> Prop), uniquant p -> SET.
(** Uniquedの性質の公理 *)
Axiom UniqueAx : forall (p : SET -> Prop) (h : uniquant p), p (UniqueSet p h).