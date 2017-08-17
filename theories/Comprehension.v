Require Import Init.

Require Import Types.

(**

公理的集合論の公理は内包により集合を定義していることが多い。

The axiom schema of comprehension

*)

(** 弱い内包 *)
Definition weak_comp (p : SET -> Prop) (a : SET) := forall x, p x -> x :e a.

(** 内包 *)
Definition comp (p : SET -> Prop) (a : SET) := forall x, x :e a <-> p x.

(** 内包は弱い内包を含意する *)
Theorem comp_include_weak_comp : forall p a, comp p a -> weak_comp p a.
Proof.
 intros p a apComp x xp.
 case (apComp x).
 intros apCompLeft apCompRight.
 apply apCompRight, xp.
Qed.

(** 内包は集合に含まれる元を定める *)
Lemma comp_stepr : forall p a b, comp p a -> comp p b -> forall x, x :e a <-> x :e b.
Proof.
 intros p a b apComp bpComp x.
 case (apComp x).
 intros apCompLeft apCompRight.
 case (bpComp x).
 intros bpCompLeft bpCompRight.
 split.
 -
  intros axIn.
  apply bpCompRight, apCompLeft, axIn.
 -
  intros bxIn.
  apply apCompRight, bpCompLeft, bxIn.
Qed.