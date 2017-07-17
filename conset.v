(* 集合を構築する定理 *)

Load IZF.

Theorem sub_refl : forall (A : SET), Sub A A.
Proof.
 unfold Sub.
 intros A x H.
 apply H.
Qed.

Theorem sub_exten : forall (A B : SET), Sub A B -> Sub B A -> A = B.
Proof.
 intros A B P Q.
 apply ExtenAx.
 intros x.
 split.
 -
  unfold Sub in P.
  apply P.
 -
  unfold Sub in Q.
  apply Q.
Qed.

Theorem sub_trans : forall (A B C : SET), Sub A B -> Sub C A -> Sub C B.
Proof.
 unfold Sub.
 intros A B C P Q x H.
 apply P.
 apply Q.
 apply H.
Qed.

Theorem sub_empty : forall (A : SET), Sub empty A.
Proof.
 unfold Sub.
 intros A x H.
 apply False_ind.
 assert (U := EmptyUx x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Theorem pair_case : forall (A B : SET) x, In x (pair A B) -> x = A \/ x = B.
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Theorem pair_ind : forall (A B : SET) x, x = A \/ x = B -> In x (pair A B).
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ur.
 apply H.
Qed.

Theorem pair_left : forall (A B : SET), In A (pair A B).
Proof.
 intros A B.
 apply pair_ind.
 left.
 reflexivity.
Qed.

Theorem pair_right : forall (A B : SET), In B (pair A B).
Proof.
 intros A B.
 apply pair_ind.
 right.
 reflexivity.
Qed.

Lemma pair_sym_exten : forall A B x, In x (pair A B) -> In x (pair B A).
Proof.
 intros A B x H.
 apply pair_ind.
 apply or_comm.
 apply pair_case.
 apply H.
Qed.

Theorem pair_sym : forall (A B : SET), pair A B = pair B A.
Proof.
 intros A B.
 apply ExtenAx.
 intros x.
 split.
 -
  apply pair_sym_exten.
 -
  apply pair_sym_exten.
Qed.

Theorem union_trans : forall (A B C : SET), In A B -> In B C -> In A (union C).
Proof.
 unfold union.
 intros A B C H I.
 assert (U := UnionUx C A).
 destruct U as [U0 U1].
 apply U1.
 exists B.
 split.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union_sub : forall (A B : SET), In A B -> Sub A (union B).
Proof.
 unfold Sub.
 intros A B H x I.
 apply union_trans with A.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union2_left : forall (A B : SET) x, In x A -> In x (union2 A B).
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with A.
 -
  apply H.
 -
  apply pair_left.
Qed.

Theorem union2_right : forall (A B : SET) x, In x B -> In x (union2 A B).
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with B.
 -
  apply H.
 -
  apply pair_right.
Qed.

Theorem union2_ind : forall (A B : SET) x, In x A \/ In x B -> In x (union2 A B).
Proof.
 intros A B x H.
 destruct H as [Hl | Hr].
 -
  apply union2_left.
  apply Hl.
 -
  apply union2_right.
  apply Hr.
Qed.

Theorem union2_case : forall (A B : SET) x, In x (union2 A B) -> In x A \/ In x B.
Proof.
 intros A B x H.
 assert (U := Union2Ux A B x).
 destruct U as [U0 U1].
 assert (U2 := U0 H).
 destruct U2 as [V0 V1].
 destruct V1 as [V1 V2].
 assert (W := pair_case A B V0 V1).
 destruct W as [I | I].
 -
  left.
  rewrite <- I.
  apply V2.
 -
  right.
  rewrite <- I.
  apply V2.
Qed.

Lemma union2_sym_exten : forall A B x, In x (union2 A B) -> In x (union2 B A).
Proof.
 intros A B x H.
 apply union2_ind.
 apply or_comm.
 apply union2_case.
 apply H.
Qed.

Theorem union2_sym : forall (A B : SET), union2 A B = union2 B A.
Proof.
 intros A B.
 apply ExtenAx.
 intro x.
 split.
 -
  apply union2_sym_exten.
 -
  apply union2_sym_exten.
Qed.