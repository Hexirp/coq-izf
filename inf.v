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

Lemma exists_nat : exists x, IsNat x.
Proof.
 apply comp_r_prom.
 destruct InfAx as [Inf Ax].
 exists (sep InNat Inf).
 unfold comp_r.
 intros x R.
 unfold IsInf in Ax.
 destruct Ax as [Axo Axs].
 unfold InNat in R.
 destruct R as [Ro Rs].
 unfold Natlike in Ro.
 destruct Ro as [Roo | Ros].
 +
  assert (U := SepUx InNat Inf x).
  destruct U as [Ul Ur].
  apply Ur.
  split.
  -
   unfold InNat.
   split.
   *
    unfold Natlike.
    left.
    rewrite Roo.
    apply eq_refl.
   *
    apply Rs.
  -
   rewrite Roo.
   apply Axo.
 +
  assert (U := SepUx InNat Inf x).
  destruct U as [Ul Ur].
  apply Ur.
  split.
  -
   unfold InNat.
   split.
   *
    unfold Natlike.
    right.
    destruct Ros as [px Ros].
    exists px.
    apply Ros.
   *
    apply (IndAx (Natlike (fun a => In a x))).
    intros a H.
    apply Rs.
  -
   unfold Natlike in Rs.
   generalize Rs.
   generalize Ros.
   generalize x.
   clear Ur.
   clear Ul.
   clear Rs.
   clear Ros.
   clear x.
   apply (IndAx (fun x0 => (exists y : SET, True /\ x0 = succ y) ->
           (forall y : SET, Natlike (fun a : SET => In a x0) y) -> In x0 Inf)).
   intros x H I J.
   destruct I as [px I].
   destruct I as [_ I].
   rewrite I.
   apply Axs.
   apply H.
   *
    rewrite I.
    apply union2_ind.
    right.
    apply pair_left.
   *
    unfold Natlike in J.

Theorem UniqueNat : Unique IsNat.
Proof.
 split.
 -
  apply comp_r_prom.