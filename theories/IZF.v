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

(** ある条件を満たしただ一つ存在する集合の省略法とその記述性

Coq.Logic.Descriptionに似た公理がある。

*)
Module Uniqueness.
 Import Types.

 (** pを満たす値がただ一つのみ存在すること。Uniqueness quantificationより命名。 *)
 Definition uniquant (A : Type) (p : A -> Prop)
  := (exists x, p x) /\ (forall x y, p x -> p y -> x = y).

 (** SETのuniquant *)
 Definition set_uniquant := uniquant SET.

 (** uniquantと既存の構文との関係 *)
 Theorem uniquant_existence (A : Type) (p : A -> Prop)
  : uniquant A p <-> exists! x, p x.
 Proof.
  apply unique_existence.
 Qed.

 (** Pを満たして一意に存在する集合 *)
 Axiom UniqueSet : forall (p : SET -> Prop), set_uniquant p -> SET.
 (** Uniquedの性質の公理 *)
 Axiom UniqueAx : forall (p : SET -> Prop) (h : set_uniquant p), p (UniqueSet p h).

 (** ただ一つのみ存在するということから集合の記述を得る。 *)
 Theorem set_description (p : SET -> Prop) : set_uniquant p -> { x : SET | p x }.
 Proof.
  intros pUni.
  exists (UniqueSet p pUni).
  apply UniqueAx.
 Qed.
End Uniqueness.

Module Extension.
 Import Types Comprehension.

 (* 外延性の公理。外延は集合の同値関係を定める。 *)
 Axiom ExtenAx : forall a b, exten a b -> a = b.

 (* 内包は同値関係を定める *)
 Lemma comp_eq : forall p a b, comp p a -> comp p b -> a = b.
 Proof.
  intros p a b apComp bpComp.
  apply ExtenAx.
  apply comp_exten with p.
  -
   apply apComp.
  -
   apply bpComp.
 Qed.

 (* 互いに部分集合である二つの集合は等しい *)
 Theorem sub_eq : forall a b, a c= b -> b c= a -> a = b.
 Proof.
  intros a b baSub abSub.
  apply ExtenAx.
  apply sub_exten.
  -
   apply baSub.
  -
   apply abSub.
 Qed.
End Extension.

Module UniExten.
 Import Types Uniqueness Comprehension Extension.

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
End UniExten.

Module Empty.
 Import Types Comprehension.

 (* 空集合である *)
 Definition IsEmpty := comp (fun _ => False).
 (* 空集合の公理 *)
 Axiom EmptyAx : exists e, IsEmpty e.
End Empty.