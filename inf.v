(* 無限集合に関する定理 *)

Load axioms.

Definition comp_r (P : SET -> Prop) (A : SET) := forall x, P x -> In x A.

Theorem comp_r_prom (P : SET -> Prop) : (exists a, comp_r P a) -> exists a, comp P a.
Proof.
 intros H.
 destruct H as [Ha HH].
 exists Ha.
 unfold comp.
 intros x.
 split.
 -
  assert (U := SepAx P Ha).
  intros Q.
  destruct U as [Ua UH].
  unfold IsSep in UH.
  unfold comp in UH.
  assert (V := UH x).
  destruct V as [Vl Vr].
  apply proj1 with (In x Ha).
  apply Vl.
 -
  intros Q.
  unfold comp_r in HH.
  apply (HH x).
  
 assert (U := SepAx P Ha).
 destruct U as [Ua UH].
 assert (Ux := UH x).

Definition IsNat (A : SET) := forall x, In x A <-> Natlike A x.