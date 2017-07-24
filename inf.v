(* 無限集合に関する定理
 *
 * 以下の文献を参考にした。
 * http://konn-san.com/math/set-theory-seminar/2012-10-30.pdf
 * https://en.wikipedia.org/wiki/Axiom_of_infinity
 *)

Load axioms.

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

Definition Natlike P x := x = empty \/ exists y, P y /\ x = succ y.

Definition InNat x := Natlike (fun _ => True) x /\ forall y, Natlike (fun a => In a x) y.

Definition IsNat_r (A : SET) := comp_r InNat A.

Definition IsNat (A : SET) := comp InNat A.

Lemma inf_then_nat_r : forall A, IsInf A -> IsNat_r A.
Proof.
 intros A H.
 unfold IsNat_r.
 unfold comp_r.
 intros x.
 unfold InNat.
 unfold Natlike.
 intros R.
 destruct R as [Ro Rs].
 destruct H as [Ho Hs].
 destruct Ro as [Oo | Os].
 -
  rewrite Oo.
  apply Ho.
 -
  destruct Os as [OX OH].
  destruct OH as [_ OH].
  rewrite OH.
  apply Hs.
Admitted.

Theorem UniqueNat : Unique IsNat.
Proof.
 split.
 -
  apply comp_r_prom.