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

 (* 空集合の使用 *)
 Theorem empty_apply : forall a : Prop, (forall x, IsEmpty x -> a) -> a.
 Proof.
  intros a p.
  case EmptyAx.
  apply p.
 Qed.

 (* 空集合の外延性 *)
 Lemma empty_exten : forall a b, IsEmpty a -> IsEmpty b -> exten a b.
 Proof.
  intros a b.
  apply comp_exten.
 Qed.
End Empty.

Import Types Uniqueness Comprehension Extension UniExten Empty.

(* 空集合の一意存在性 *)
Theorem UniqueEmpty : uniquant SET IsEmpty.
Proof.
 apply comp_unique.
 apply EmptyAx.
Qed.
(* 空集合 *)
Definition empty := UniqueSet IsEmpty UniqueEmpty.
(* 空集合の単一性 *)
Definition EmptyUx := UniqueAx IsEmpty UniqueEmpty.

Definition IsPair (A : SET) (B : SET) := comp (fun x => x = A \/ x = B).
(* 対の公理 *)
Axiom PairAx : forall a b, exists c, IsPair a b c.
Theorem UniquePair : forall (A : SET) (B : SET), uniquant SET (IsPair A B).
Proof.
 intros A B.
 apply comp_unique.
 apply PairAx.
Qed.
Definition pair (A : SET) (B : SET) := UniqueSet (IsPair A B) (UniquePair A B).
Definition singleton (A : SET) := pair A A.
Definition PairUx (A : SET) (B : SET) := UniqueAx (IsPair A B) (UniquePair A B).

Definition IsUnion (A : SET) := comp (fun x => exists u, u :e A /\ x :e u).
(* 和集合公理 *)
Axiom UnionAx : forall a, exists b, IsUnion a b.
Theorem UniqueUnion : forall (A : SET), uniquant SET (IsUnion A).
Proof.
 intros A.
 apply comp_unique.
 apply UnionAx.
Qed.
Definition union (A : SET) := UniqueSet (IsUnion A) (UniqueUnion A).
Definition union2 (A : SET) (B : SET) := union (pair A B).
Definition UnionUx (A : SET) := UniqueAx (IsUnion A) (UniqueUnion A).
Definition Union2Ux (A : SET) (B : SET) := UnionUx (pair A B).

Definition IsPower (A : SET) := comp (fun x => x c= A).
(* 冪集合公理 *)
Axiom PowerAx : forall a, exists b, IsPower a b.
Theorem UniquePower : forall (A : SET), uniquant SET (IsPower A).
Proof.
 intros A.
 apply comp_unique.
 apply PowerAx.
Qed.
Definition power (A : SET) := UniqueSet (IsPower A) (UniquePower A).
Definition PowerUx (A : SET) := UniqueAx (IsPower A) (UniquePower A).

(* 後者関数 *)
Definition succ (A : SET) := union2 A (singleton A).
Definition IsInf (A : SET) := In empty A /\ (forall n, In n A -> succ n :e A).
(* 無限公理 *)
Axiom InfAx : exists a, IsInf a.

Definition IsSep (P : SET -> Prop) (A : SET) := comp (fun x => P x /\ x :e A).
(* 分出公理 *)
Axiom SepAx : forall p a, exists b, IsSep p a b.
Theorem UniqueSep : forall (P : SET -> Prop) (A : SET), uniquant SET (IsSep P A).
Proof.
 intros P A.
 apply comp_unique.
 apply SepAx.
Qed.
Definition sep (P : SET -> Prop) (A : SET) := UniqueSet (IsSep P A) (UniqueSep P A).
Definition SepUx (P : SET -> Prop) (A : SET) := UniqueAx (IsSep P A) (UniqueSep P A).

(* 集合に対する帰納法の公理 *)
Axiom IndAx : forall (P : SET -> Prop),
 (forall a, (forall x, x :e a -> P x) -> P a) -> forall a, P a.

(* 値域が宇宙である多価関数である *)
Definition mf_u (P : SET -> SET -> Prop) (A : SET) := forall x, x :e A -> exists y, P x y.
(* 値域が宇宙である多価関数のそれぞれの値を少なくとも一つ含む集合である *)
Definition col (P : SET -> SET -> Prop) (A : SET) (B : SET)
 := forall x, x :e A -> exists y, y :e B /\ P x y.
(* 収集公理 *)
Axiom ColAx : forall (P : SET -> SET -> Prop) a, mf_u P a -> exists b, col P a b.

Theorem sub_refl : forall (A : SET), A c= A.
Proof.
 unfold sub.
 intros A x H.
 apply H.
Qed.

Theorem sub_exten : forall (A B : SET), A c= B -> B c= A -> A = B.
Proof.
 intros A B P Q.
 apply ExtenAx.
 intros x.
 split.
 -
  unfold sub in P.
  apply P.
 -
  unfold sub in Q.
  apply Q.
Qed.

Theorem sub_trans : forall (A B C : SET), A c= B -> C c= A -> sub C B.
Proof.
 unfold sub.
 intros A B C P Q x H.
 apply P.
 apply Q.
 apply H.
Qed.

Theorem sub_empty : forall (A : SET), empty c= A.
Proof.
 unfold sub.
 intros A x H.
 apply False_ind.
 assert (U := EmptyUx x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Theorem pair_case : forall (A B : SET) x, x :e pair A B -> x = A \/ x = B.
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Theorem pair_ind : forall (A B : SET) x, x = A \/ x = B -> x :e pair A B.
Proof.
 unfold pair.
 intros A B x H.
 assert (U := PairUx A B x).
 destruct U as [Ul Ur].
 apply Ur.
 apply H.
Qed.

Theorem pair_left : forall (A B : SET), A :e pair A B.
Proof.
 intros A B.
 apply pair_ind.
 left.
 reflexivity.
Qed.

Theorem pair_right : forall (A B : SET), B :e pair A B.
Proof.
 intros A B.
 apply pair_ind.
 right.
 reflexivity.
Qed.

Lemma pair_sym_exten : forall A B x, x :e pair A B -> x :e pair B A.
Proof.
 intros A B x H.
 apply pair_ind.
 apply or_comm.
 apply pair_case.
 apply H.
Qed.

Theorem pair_sym : forall (A B : SET), pair A B = pair B A.
Proof.
 intros A B.
 apply ExtenAx.
 intros x.
 split.
 -
  apply pair_sym_exten.
 -
  apply pair_sym_exten.
Qed.

Theorem union_trans : forall (A B C : SET), A :e B -> B :e C -> A :e union C.
Proof.
 unfold union.
 intros A B C H I.
 assert (U := UnionUx C A).
 destruct U as [U0 U1].
 apply U1.
 exists B.
 split.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union_sub : forall (A B : SET), A :e B -> sub A (union B).
Proof.
 unfold sub.
 intros A B H x I.
 apply union_trans with A.
 -
  apply I.
 -
  apply H.
Qed.

Theorem union2_left : forall (A B : SET) x, x :e A -> x :e union2 A B.
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with A.
 -
  apply H.
 -
  apply pair_left.
Qed.

Theorem union2_right : forall (A B : SET) x, x :e B -> x :e union2 A B.
Proof.
 unfold union2.
 intros A B x H.
 apply union_trans with B.
 -
  apply H.
 -
  apply pair_right.
Qed.

Theorem union2_ind : forall (A B : SET) x, x :e A \/ x :e B -> x :e union2 A B.
Proof.
 intros A B x H.
 destruct H as [Hl | Hr].
 -
  apply union2_left.
  apply Hl.
 -
  apply union2_right.
  apply Hr.
Qed.

Lemma union2_case_eq : forall A B C x, x :e C -> C = A \/ C = B -> x :e A \/ x :e B.
Proof.
 intros A B C x H R.
 destruct R as [RA | RB].
 -
  left.
  rewrite <- RA.
  apply H.
 -
  right.
  rewrite <- RB.
  apply H.
Qed.

Lemma union2_case_pair : forall A B C x, x :e C -> C :e pair A B -> x :e A \/ x :e B.
Proof.
 intros A B C x H P.
 apply union2_case_eq with C.
 -
  apply H.
 -
  assert (U := PairUx A B C).
  destruct U as [Ul Ur].
  apply Ul.
  apply P.
Qed.

Lemma union2_case_exists : forall A B x,
 (exists C, C :e pair A B /\ x :e C) -> x :e A \/ x :e B.
Proof.
 intros A B x H.
 destruct H as [C P].
 destruct P as [PC Px].
 apply union2_case_pair with C.
 -
  apply Px.
 -
  apply PC.
Qed.

Theorem union2_case : forall (A B : SET) x, x :e union2 A B -> x :e A \/ x :e B.
Proof.
 intros A B x H.
 apply union2_case_exists.
 assert (U := Union2Ux A B x).
 destruct U as [Ul Ur].
 apply Ul.
 apply H.
Qed.

Lemma union2_sym_exten : forall A B x, x :e union2 A B -> x :e union2 B A.
Proof.
 intros A B x H.
 apply union2_ind.
 apply or_comm.
 apply union2_case.
 apply H.
Qed.

Theorem union2_sym : forall (A B : SET), union2 A B = union2 B A.
Proof.
 intros A B.
 apply ExtenAx.
 intros x.
 split.
 -
  apply union2_sym_exten.
 -
  apply union2_sym_exten.
Qed.

Lemma union2_trans_exten : forall A B C x,
 x :e union2 A (union2 B C) -> x :e union2 (union2 A B) C.
Proof.
 intros A B C x H.
 apply union2_ind.
 assert (forall a b, In x a \/ In x b <-> In x (union2 a b)) as P.
 -
  intros a b.
  split.
  +
   apply union2_ind.
  +
   apply union2_case.
 -
  assert (Q := or_iff_compat_r (x :e C) (P A B)).
  destruct Q as [Ql Qr].
  apply Ql.
  apply or_assoc.
  assert (R := or_iff_compat_l (x :e A) (P B C)).
  destruct R as [Rl Rr].
  apply Rr.
  apply union2_case.
  apply H.
Qed.

Theorem union2_trans : forall (A B C : SET), union2 A (union2 B C) = union2 (union2 A B) C.
Proof.
 intros A B C.
 apply ExtenAx.
 intros x.
 split.
 -
  apply union2_trans_exten.
 -
  rewrite (union2_sym (union2 A B) C).
  rewrite (union2_sym A B).
  rewrite (union2_sym A (union2 B C)).
  rewrite (union2_sym B C).
  apply union2_trans_exten.
Qed.

Theorem union2_empty : forall (A : SET), union2 empty A = A.
Proof.
 intros A.
 apply ExtenAx.
 intros x.
 split.
 -
  intros H.
  apply union2_case in H.
  destruct H as [He | HA].
  +
   apply False_ind.
   assert (U := EmptyUx x).
   destruct U as [Ul Ur].
   apply Ul.
   apply He.
  +
   apply HA.
 -
  intros H.
  apply union2_ind.
  right.
  apply H.
Qed.