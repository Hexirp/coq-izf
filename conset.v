(* 集合を構築する定理 *)

Load IZF.

Theorem sub_refl : forall (A : SET), Sub A A.
Proof.
 intro A.
 unfold Sub.
 intros x H.
 apply H.
Qed.

Theorem sub_exten : forall (A B : SET), Sub A B -> Sub B A -> A = B.
Proof.
 intros A B P Q.
 apply ExtenAx.
 intro x.
 split.
 -
  apply P.
 -
  apply Q.
Qed.

Theorem sub_trans : forall (A B C : SET), Sub A B -> Sub B C -> Sub A C.
Proof.
 intros A B C P Q.
 unfold Sub.
 intros x H.
 unfold Sub in P, Q.
 apply Q, P, H.
Qed.

Theorem pair_left : forall (A B : SET), In A (pair A B).
Proof.
 intros A B.
 unfold pair.
 assert (U := PairUx A B A).
 destruct U as [U0 U1].
 apply U1.
 left.
 reflexivity.
Qed.

Theorem pair_right : forall (A B : SET), In B (pair A B).
Proof.
 intros A B.
 unfold pair.
 assert (U := PairUx A B B).
 destruct U as [U0 U1].
 apply U1.
 right.
 reflexivity.
Qed.

Theorem pair_sym : forall (A B : SET), pair A B = pair B A.
Proof.
 intros A B.
 apply ExtenAx.
 intro x.
 split.
 -
  intro H.
  assert (U := PairUx A B x).
  destruct U as [U0 U1].
  assert (U2 := U0 H).
  destruct U2.
  +
   rewrite H0.
   apply pair_right.
  +
   rewrite H0.
   apply pair_left.
 -
  intro H.
  assert (U := PairUx B A x).
  destruct U as [U0 U1].
  assert (U2 := U0 H).
  destruct U2 as [I | I].
  +
   rewrite I.
   apply pair_right.
  +
   rewrite I.
   apply pair_left.
Qed.

Theorem union_trans : forall (A B C : SET), In A B -> In B C -> In A (union C).
Proof.
 intros A B C H I.
 assert (U := UnionUx C A).
 destruct U as [U0 U1].
 assert (exists x, In x C /\ In A x).
 -
  exists B.
  split.
  +
   apply I.
  +
   apply H.
 -
  assert (U2 := U1 H0).
  unfold union.
  apply U2.
Qed.

Theorem union_sub : forall (A B : SET), In A B -> Sub A (union B).
Proof.
 intros A B H.
 unfold Sub.
 intros x I.
 apply union_trans with A.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union2_left : forall (A B : SET) x, In x A -> In x (union2 A B).
Proof.
 intros A B x H.
 unfold union2.
 apply union_trans with A.
 -
  apply H.
 -
  apply pair_left.
Qed.

Theorem union2_right : forall (A B : SET) x, In x B -> In x (union2 A B).
Proof.
 intros A B x H.
 unfold union2.
 apply union_trans with B.
 -
  apply H.
 -
  apply pair_right.
Qed.

Theorem union2_case : forall (A B : SET) x, In x (union2 A B) -> In x A \/ In x B.
Proof.
 intros A B x H.
 assert (U := Union2Ux A B x).
 destruct U as [U0 U1].
 assert (U2 := U0 H).
 destruct U2 as [V0 V1].
 destruct V1 as [V1 V2].
 assert (W := PairUx A B V0).
 destruct W as [W0 W1].
 assert (W2 := W0 V1).
 destruct W2 as [I | I].
 -
  left.
  rewrite <- I.
  apply V2.
 -
  right.
  rewrite <- I.
  apply V2.
Qed.

Theorem union2_sym : forall (A B : SET), union2 A B = union2 B A.
Proof.
 intros A B.
 apply ExtenAx.
 intro x.
 split.
 -
  intro H.
  apply union2_case in H.
  destruct H as [H | H].
  +
   apply union2_right.
   apply H.
  +
   apply union2_left.
   apply H.
 -
  intro H.
  apply union2_case in H.
  destruct H as [H | H].
  +
   apply union2_right.
   apply H.
  +
   apply union2_left.
   apply H.
Qed.