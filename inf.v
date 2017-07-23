(* 無限集合に関する定理 *)

Load axioms.

Definition Natlike A x := x = empty \/ exists y, In y A /\ x = succ y.
Definition IsNat (A : SET) := forall x, In x A <-> Natlike A x.

Theorem ExistsNat : exists x, IsNat x.
Proof.
 destruct InfAx as [Inf Ax].
 exists (sep (Natlike Inf) Inf).
 intros x.
 assert (U := SepUx (Natlike Inf) Inf x).
 apply (iff_trans U).
 split.
 -
  unfold Natlike.
  intros H.
  destruct H as [HN HI].
  destruct HN as [O | S].
  +
   left.
   apply O.
  +
   right.
   destruct S as [S SH].
   destruct SH as [SI Sx].
   exists S.
   split.
   *
    assert (V := SepUx (Natlike Inf) Inf S).
    destruct V as [Vl Vr].
    apply Vr.
    split.
    --
     unfold Natlike.
     right.
    --
     apply SI.
   *
    apply Sx.

Theorem UniqueNat : Unique IsNat.
Proof.
 unfold Unique.
 split.
 -
  apply ExistsNat.