Require Import Init.

Require Import Types Uniqueness Comprehension.

(* 外延性の公理 *)
Axiom ExtenAx : forall a b, (forall x, x :e a <-> x :e b) -> a = b.

(* 内包は同値関係を定める *)
Lemma comp_exten : forall p a b, comp p a /\ comp p b -> a = b.
Proof.
 intros p a b abAnd.
 case abAnd.
 intros apComp bpComp.
 apply ExtenAx.
 revert apComp bpComp.
 apply comp_stepr.
Qed.

(* 互いに部分集合である二つの集合は等しい *)
Theorem sub_exten : forall a b, a c= b -> b c= a -> a = b.
Proof.
 intros a b baSub abSub.
 apply ExtenAx.
 intros x.
 split.
 -
  apply baSub.
 -
  apply abSub.
Qed.