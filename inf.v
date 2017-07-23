(* 無限集合に関する定理
 *
 * 以下の文献を参考にした。
 * http://konn-san.com/math/set-theory-seminar/2012-10-30.pdf
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

Definition IsNat (A : SET) := forall x, In x A <-> Natlike A x.