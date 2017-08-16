(* 無限集合に関する定理
 *
 * 以下の文献を参考にした。
 * http://konn-san.com/math/set-theory-seminar/2012-10-30.pdf
 * https://en.wikipedia.org/wiki/Axiom_of_infinity
 *)

Load constructing.

Definition comp_r (P : SET -> Prop) (A : SET) := forall x, P x -> In x A.

Theorem comp_r_prom (P : SET -> Prop) : (exists a, comp_r P a) -> exists a, comp P a.
Proof.
 intros H.
 destruct H as [Ha HH].
 exists (sep P Ha).
 unfold comp.
 intros x.
 split.
 -
  intros H.
  assert (U := SepUx P Ha x).
  destruct U as [Ul Ur].
  apply proj1 with (In x Ha).
  apply Ul.
  apply H.
 -
  intros H.
  assert (U := SepUx P Ha x).
  destruct U as [Ul Ur].
  apply Ur.
  split.
  +
   apply H.
  +
   unfold comp_r in HH.
   apply HH.
   apply H.
Qed.

Definition InNat n
 := (n = empty \/ exists k, n = succ k) /\ (forall m, m :e n -> exists k, k :e n /\m = succ k).

Fixpoint nats (n : nat) : SET :=
 match n with
 | O => empty
 | S n' => succ (nats n')
 end.

Lemma or_map_l : forall (A B C : Prop), (B -> C) -> A \/ B -> A \/ C.
Proof.
 intros A B C f x.
 case x; auto.
Qed.

Lemma or_delta : forall A, A \/ A -> A.
Proof.
 intros A x.
 case x; auto.
Qed.

Lemma succ_case : forall A x, x :e succ A -> x :e A \/ x = A.
Proof.
 intros A x H.
 apply or_map_l with (x :e singleton A).
 -
  intros I.
  apply or_delta.
  apply pair_case.
  apply I.
 -
  apply union2_case.
  apply H.
Qed.

Lemma nats_in_nat : forall n, InNat (nats n).
Proof.
 intros n.
 induction n.
 -
  unfold nats.
  unfold InNat.
  split.
  +
   left.
   reflexivity.
  +
   intros m H.
   assert (U := EmptyUx m).
   destruct U as [Ul Ur].
   apply False_ind.
   apply Ul.
   apply H.
 -
  unfold InNat.
  split.
  +
   right.
   exists (nats n).
   reflexivity.
  +
   intros m H.
   replace (nats (S n)) with (succ (nats n)) in H.
   *
    apply succ_case in H.
    destruct H as [Hp | H].
    --
     destruct IHn as [IHnO IHnS].
     

Definition IsNat (A : SET) := comp InNat A.

Theorem exists_nat : exists x, IsNat x.
Proof.
 apply comp_r_prom.
 destruct InfAx as [Inf Ax].
 exists Inf.
 unfold comp_r.
 apply (IndAx (fun x => InNat x -> x :e Inf)).
 intros x Ix R.
 unfold IsInf in Ax.
 destruct Ax as [Axo Axs].
 unfold InNat in R.
 destruct R as [Ro Rs].
 unfold Natlike in Ro.
 destruct Ro as [Roo | Ros].
 -
  rewrite Roo.
  apply Axo.
 -
  destruct Ros as [px Ros].
  destruct Ros as [_ Ros].
  rewrite Ros in Rs.
  unfold Natlike in Rs.
  rewrite Ros.
  apply Axs.
  apply Ix.
  +
   rewrite Ros.
   unfold succ.
   apply union2_right.
   apply pair_left.
  +
   unfold InNat.
   split.
   *
    unfold Natlike.
    unfold Natlike in Rs.
    destruct (Rs px) as [Rso | Rss].
    --
     left.
     apply Rso.
    --
     right.
     destruct Rss as [ppx Rss].
     exists ppx.
     split.
     ++
      apply I.
     ++
      destruct Rss as [_ Rss].
      apply Rss.
   *
    apply (IndAx (Natlike (fun a : SET => a :e px))).
    intros y Iy.
    unfold Natlike.
    unfold Natlike in Iy.

Theorem UniqueNat : Unique IsNat.
Proof.
 split.
 -
  apply comp_r_prom.