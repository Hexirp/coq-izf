Require Import Init.

Require Import Types Uniqueness Comprehension.

(* 外延性の公理。外延は集合の同値関係を定める。 *)
Axiom ExtenAx : forall a b, exten a b -> a = b.

(* 内包は同値関係を定める *)
Lemma comp_eq : forall p a b, comp p a /\ comp p b -> a = b.
Proof.
 intros p a b abAnd.
 case abAnd.
 intros apComp bpComp.
 apply ExtenAx.
 apply comp_exten with p.
 -
  apply apComp.
 -
  apply bpComp.
Qed.

(* 互いに部分集合である二つの集合は等しい *)
Theorem sub_eq : forall a b, a c= b -> b c= a -> a = b.
Proof.
 intros a b baSub abSub.
 apply ExtenAx.
 apply sub_exten.
 -
  apply baSub.
 -
  apply abSub.
Qed.