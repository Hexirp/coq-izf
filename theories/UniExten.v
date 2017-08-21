Require Import Init.

Require Import Types Uniqueness Comprehension Extension.

Lemma comp_unique : forall p, (exists a, comp p a) -> set_uniquant (comp p).
Proof.
 intros p pCompEx.
 case pCompEx.
 intros x xpComp.
 split.
 -
  exists x.
  apply xpComp.
 -
  intros y y'.
  apply comp_eq.
Qed.