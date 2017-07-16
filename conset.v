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
 apply (comp_l (fun _ => False)) with (a := empty) (x := x).
 apply EmptyUx.
 apply H.
Qed.

Theorem pair_case : forall (A B : SET) x, In x (pair A B) -> x = A \/ x = B.
Proof.
 unfold pair.
 intros A B.
 apply comp_l.
 apply PairUx.
Qed.

Theorem pair_ind : forall (A B : SET) x, x = A \/ x = B -> In x (pair A B).
Proof.
 unfold pair.
 intros A B.
 apply comp_r.
 apply PairUx.
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

Theorem or_sym : forall A B, A \/ B -> B \/ A.
Proof.
 intros A B H.
 destruct H as [Hl | Hr].
 -
  right.
  apply Hl.
 -
  left.
  apply Hr.
Qed.

Lemma pair_sym_exten : forall A B x, In x (pair A B) -> In x (pair B A).
Proof.
 intros A B x H.
 apply pair_ind.
 apply or_sym.
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