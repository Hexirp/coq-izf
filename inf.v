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

Definition Natlike P x := x = empty \/ exists y, P y /\ x = succ y.

Definition InNat x := Natlike (fun _ => True) x /\ forall y, Natlike (fun a => In a x) y.

Definition IsNat_r (A : SET) := comp_r InNat A.

Definition IsNat (A : SET) := comp InNat A.

(*

IsNatを満たす集合は存在することを示す。そのためにInNatが成り立つすべての集合を含む集合が存在することを示す。
そのためにそれが無限公理により存在が保証される無限集合であることを示す。

*)

Lemma exists_nat : exists x, IsNat x.
Proof.
 apply comp_r_prom.
 destruct InfAx as [Inf Ax].
 exists Inf.
 unfold comp_r.
 intros x R.
 unfold IsInf in Ax.
 destruct Ax as [Axo Axs].
 unfold InNat in R.
 destruct R as [Ro Rs].
 unfold Natlike in Ro.
 destruct Ro as [Roo | Ros].
 +
  rewrite Roo.
  apply Axo.
 +
  destruct Ros as [px Ros].
  destruct Ros as [_ Ros].
  generalize Rs; clear Rs.
  generalize Ros; clear Ros.
  generalize px; clear px.
  apply (IndAx (
   fun px =>
    x = succ px ->
     (forall y : SET, Natlike (fun a : SET => a :e x) y) ->
      x :e Inf)).
  intros.

Theorem UniqueNat : Unique IsNat.
Proof.
 split.
 -
  apply comp_r_prom.