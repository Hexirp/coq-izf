Require Import Init.

(** 最も基本的な型 *)
Module Types.
 (** 集合の型 *)
 Parameter SET : Type.
 (** 帰属関係の述語 *)
 Axiom In : SET -> SET -> Prop.
 (** 帰属関係の記法。∈の見立て。 *)
 Notation "x ':e' y" := (In x y) (at level 70).
 (** 帰属関係の否定。∉の見立て。 *)
 Notation "x ':/e ' y" := (~ In x y) (at level 70).

 (** 集合により限定された全称量化 *)
 Notation "'forall' x ':e' a ',' p"
  := (forall x : SET, x :e a -> p) (at level 199, x ident, right associativity) : type_scope.
 (** 集合により限定された存在量化 *)
 Notation "'exists' x ':e' a ',' p"
  := (exists x : SET, x :e a /\ p) (at level 199, x ident, right associativity) : type_scope.

 (* 包含関係 *)
 Definition sub (a b : SET) := forall x, x :e a -> x :e b.
 (* 包摂関係の記法。⊂の見立て。 *)
 Notation "x 'c=' y" := (sub x y) (at level 70) : type_scope.
 Notation "x 'c/=' y" := (~ sub x y) (at level 70) : type_scope.
 (* 反射律 *)
 Theorem sub_refl (a : SET) : sub a a.
 Proof.
  intros x axIn.
  apply axIn.
 Qed.
 (* 推移律 *)
 Theorem sub_trans (a b c : SET) : sub a b -> sub b c -> sub a c.
 Proof.
  intros baExten cbExten x axIn.
  apply cbExten.
  apply baExten.
  apply axIn.
 Qed.

 (* 外延 *)
 Definition exten (a b : SET) := forall x, x :e a <-> x :e b.
 (* 反射律 *)
 Theorem exten_refl (a : SET) : exten a a.
 Proof.
  intros x.
  apply iff_refl.
 Qed.
 (* 対称律 *)
 Theorem exten_sym (a b : SET) : exten a b -> exten b a.
 Proof.
  intros baExten x.
  apply iff_sym.
  apply baExten.
 Qed.
 (* 推移律 *)
 Theorem exten_trans (a b c : SET) : exten a b -> exten b c -> exten a c.
 Proof.
  intros baExten cbExten x.
  apply iff_trans with (x :e b).
  -
   apply baExten.
  -
   apply cbExten.
 Qed.
 (* 互いに部分集合である二つの集合は外延である *)
 Theorem sub_exten (a b : SET) : a c= b -> b c= a -> exten a b.
 Proof.
  intros baSub abSub x.
  split.
  -
   apply baSub.
  -
   apply abSub.
 Qed.
End Types.

(** 内包

公理的集合論の公理は内包により集合を定義していることが多い。

*)
Module Comprehension.
 Import Types.

 (** 弱い内包 *)
 Definition weak_comp (p : SET -> Prop) (a : SET) := forall x, p x -> x :e a.

 (** 内包 *)
 Definition comp (p : SET -> Prop) (a : SET) := forall x, x :e a <-> p x.

 (** 内包は弱い内包を含意する *)
 Theorem comp_include_weak_comp : forall p a, comp p a -> weak_comp p a.
 Proof.
  intros p a apComp x xp.
  case (apComp x).
  intros apCompLeft apCompRight.
  apply apCompRight, xp.
 Qed.

 (** 内包は外延を導く *)
 Lemma comp_exten : forall p a b, comp p a -> comp p b -> exten a b.
 Proof.
  intros p a b apComp bpComp x.
  case (apComp x).
  intros apCompLeft apCompRight.
  case (bpComp x).
  intros bpCompLeft bpCompRight.
  split.
  -
   intros axIn.
   apply bpCompRight.
   apply apCompLeft.
   apply axIn.
  -
   intros bxIn.
   apply apCompRight.
   apply bpCompLeft.
   apply bxIn.
 Qed.
End Comprehension.