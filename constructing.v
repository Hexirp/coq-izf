(* 集合を構築する定理 *)

Load axioms.

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

Theorem pair_case : forall (A B : SET) x, x :e pair A B -> x = A \/ x = B.
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Theorem pair_ind : forall (A B : SET) x, x = A \/ x = B -> x :e pair A B.
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ur.
 apply H.
Qed.

Theorem pair_left : forall (A B : SET), A :e pair A B.
Proof.
 intros A B.
 apply pair_ind.
 left.
 reflexivity.
Qed.

Theorem pair_right : forall (A B : SET), B :e pair A B.
Proof.
 intros A B.
 apply pair_ind.
 right.
 reflexivity.
Qed.

Lemma pair_sym_exten : forall A B x, x :e pair A B -> x :e pair B A.
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

Theorem union_trans : forall (A B C : SET), A :e B -> B :e C -> A :e union C.
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

Theorem union_sub : forall (A B : SET), A :e B -> Sub A (union B).
Proof.
 unfold Sub.
 intros A B H x I.
 apply union_trans with A.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union2_left : forall (A B : SET) x, x :e A -> x :e union2 A B.
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with A.
 -
  apply H.
 -
  apply pair_left.
Qed.

Theorem union2_right : forall (A B : SET) x, x :e B -> x :e union2 A B.
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with B.
 -
  apply H.
 -
  apply pair_right.
Qed.

Theorem union2_ind : forall (A B : SET) x, x :e A \/ x :e B -> x :e union2 A B.
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

Lemma union2_case_eq : forall A B C x, x :e C -> C = A \/ C = B -> x :e A \/ x :e B.
Proof.
 intros A B C x H R.
 destruct R as [RA | RB].
 -
  left.
  rewrite <- RA.
  apply H.
 -
  right.
  rewrite <- RB.
  apply H.
Qed.

Lemma union2_case_pair : forall A B C x, x :e C -> C :e pair A B -> x :e A \/ x :e B.
Proof.
 intros A B C x H P.
 apply union2_case_eq with C.
 -
  apply H.
 -
  assert (U := PairUx A B C).
  destruct U as [Ul Ur].
  apply Ul.
  apply P.
Qed.

Lemma union2_case_exists : forall A B x,
 (exists C, C :e pair A B /\ x :e C) -> x :e A \/ x :e B.
Proof.
 intros A B x H.
 destruct H as [C P].
 destruct P as [PC Px].
 apply union2_case_pair with C.
 -
  apply Px.
 -
  apply PC.
Qed.

Theorem union2_case : forall (A B : SET) x, x :e union2 A B -> x :e A \/ x :e B.
Proof.
 intros A B x H.
 apply union2_case_exists.
 assert (U := Union2Ux A B x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Lemma union2_sym_exten : forall A B x, x :e union2 A B -> x :e union2 B A.
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
 intros x.
 split.
 -
  apply union2_sym_exten.
 -
  apply union2_sym_exten.
Qed.

Lemma union2_trans_exten : forall A B C x,
 x :e union2 A (union2 B C) -> x :e union2 (union2 A B) C.
Proof.
 intros A B C x H.
 apply union2_ind.
 assert (forall a b, In x a \/ In x b <-> In x (union2 a b)) as P.
 -
  intros a b.
  split.
  +
   apply union2_ind.
  +
   apply union2_case.
 -
  assert (Q := or_iff_compat_r (x :e C) (P A B)).
  destruct Q as [Ql Qr].
  apply Ql.
  apply or_assoc.
  assert (R := or_iff_compat_l (x :e A) (P B C)).
  destruct R as [Rl Rr].
  apply Rr.
  apply union2_case.
  apply H.
Qed.

Theorem union2_trans : forall (A B C : SET), union2 A (union2 B C) = union2 (union2 A B) C.
Proof.
 intros A B C.
 apply ExtenAx.
 intros x.
 split.
 -
  apply union2_trans_exten.
 -
  rewrite (union2_sym (union2 A B) C).
  rewrite (union2_sym A B).
  rewrite (union2_sym A (union2 B C)).
  rewrite (union2_sym B C).
  apply union2_trans_exten.
Qed.

Theorem union2_empty : forall (A : SET), union2 empty A = A.
Proof.
 intros A.
 apply ExtenAx.
 intros x.
 split.
 -
  intros H.
  apply union2_case in H.
  destruct H as [He | HA].
  +
   apply False_ind.
   assert (U := EmptyUx x).
   destruct U as [Ul Ur].
   apply Ul.
   apply He.
  +
   apply HA.
 -
  intros H.
  apply union2_ind.
  right.
  apply H.
Qed.