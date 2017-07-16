(* 以下の文献を参考にした。
 * http://shirodanuki.cs.shinshu-u.ac.jp/TPP/TPP2013_satou.pdf （間違いが多いので注意）
 * https://plato.stanford.edu/entries/set-theory-constructive/axioms-CZF-IZF.html
 *)

Require Import Init.

(* 集合の型 *)
Axiom SET : Type.
(* 帰属関係の述語 *)
Axiom In : SET -> SET -> Prop.

(* 包含関係 *)
Definition Sub (A : SET) (B : SET) := forall x, In x A -> In x B.

(* ある述語を満たす集合が一つのみである *)
Definition Unique (P : SET -> Prop) := (exists x, P x) /\ (forall x y, P x /\ P y -> x = y).
(* Pを満たして一意に存在する集合 *)
Axiom Uniqued : forall (P : SET -> Prop), Unique P -> SET.
(* Uniquedの性質の公理 *)
Axiom UniqueAx : forall (P : SET -> Prop) (U : Unique P), P (Uniqued P U).

(* 外延性の公理 *)
Axiom ExtenAx : forall a b, (forall x, In x a <-> In x b) -> a = b.

(* 空集合である *)
Definition IsEmpty (A : SET) := forall x, not (In x A).
(* 空集合の公理 *)
Axiom EmptyAx : exists e, IsEmpty e.
(* 空集合の一意存在性 *)
Theorem UniqueEmpty : Unique IsEmpty.
Proof.
 unfold Unique.
 split.
 - (* 空集合の存在性 *)
  apply EmptyAx.
 - (* 空集合の一意性 *)
  intros x y H.
  destruct H as [Hx Hy].
  apply ExtenAx.
  intros z.
  split.
  + (* 右への含意 *)
   intros H0.
   apply False_ind.
   unfold IsEmpty in Hx.
   apply Hx with z.
   apply H0.
  + (* 左への含意 *)
   intros H0.
   apply False_ind.
   unfold IsEmpty in Hy.
   apply Hy with z.
   apply H0.
Qed.
(* 空集合 *)
Definition empty := Uniqued IsEmpty UniqueEmpty.
(* 空集合の単一性 *)
Definition EmptyUx := UniqueAx IsEmpty UniqueEmpty.

Definition IsPair (A : SET) (B : SET) (C : SET) := forall x, In x C <-> x = A \/ x = B.
(* 対の公理 *)
Axiom PairAx : forall a b, exists c, IsPair a b c.
Theorem UniquePair : forall (A : SET) (B : SET), Unique (IsPair A B).
Proof.
 intros A B.
 unfold Unique.
 split.
 -
  apply PairAx.
 -
  intros x y H.
  apply ExtenAx.
  intros z.
  destruct H as [Hx Hy].
  apply iff_stepl with (z = A \/ z = B).
  +
   unfold IsPair in Hy.
   apply iff_sym.
   apply Hy.
  +
   unfold IsPair in Hx.
   apply iff_sym.
   apply Hx.
Qed.
Definition pair (A : SET) (B : SET) := Uniqued (IsPair A B) (UniquePair A B).
Definition singleton (A : SET) := pair A A.
Definition PairUx (A : SET) (B : SET) := UniqueAx (IsPair A B) (UniquePair A B).

Definition IsUnion (A : SET) (B : SET) := forall x, In x B <-> exists u, In u A /\ In x u.
(* 和集合公理 *)
Axiom UnionAx : forall a, exists b, IsUnion a b.
Theorem UniqueUnion : forall (A : SET), Unique (IsUnion A).
Proof.
 intros A.
 unfold Unique.
 split.
 -
  apply UnionAx.
 -
  intros x y H.
  apply ExtenAx.
  intros z.
  destruct H as [Hx Hy].
  apply iff_stepl with (exists u : SET, In u A /\ In z u).
  +
   unfold IsUnion in Hy.
   apply iff_sym.
   apply Hy.
  +
   unfold IsUnion in Hx.
   apply iff_sym.
   apply Hx.
Qed.
Definition union (A : SET) := Uniqued (IsUnion A) (UniqueUnion A).
Definition union2 (A : SET) (B : SET) := union (pair A B).
Definition UnionUx (A : SET) := UniqueAx (IsUnion A) (UniqueUnion A).
Definition Union2Ux (A : SET) (B : SET) := UnionUx (pair A B).


Definition IsPower (A : SET) (B : SET) := forall x, In x B <-> Sub x A.
(* 冪集合公理 *)
Axiom PowerAx : forall a, exists b, IsPower a b.
Theorem UniquePower : forall (A : SET), Unique (IsPower A).
Proof.
 intros A.
 unfold Unique.
 split.
 -
  apply PowerAx.
 -
  intros x y H.
  apply ExtenAx.
  intro z.
  destruct H as [Hx Hy].
  apply iff_stepl with (Sub z A).
  +
   unfold IsPower in Hy.
   apply iff_sym.
   apply Hy.
  +
   unfold IsPower in Hx.
   apply iff_sym.
   apply Hx.
Qed.
Definition power (A : SET) := Uniqued (IsPower A) (UniquePower A).
Definition PowerUx (A : SET) := UniqueAx (IsPower A) (UniquePower A).

(* 後者関数 *)
Definition succ (A : SET) := union2 A (singleton A).
Definition IsInf (A : SET) := In empty A /\ (forall n, In n A -> In (succ n) A).
(* 無限公理 *)
Axiom InfAx : exists a, IsInf a.

Definition IsSep (P : SET -> Prop) (A : SET) (B : SET) := forall x, In x B <-> P x /\ In x A.
(* 分出公理 *)
Axiom SepAx : forall p a, exists b, IsSep p a b.
Theorem UniqueSep : forall (P : SET -> Prop) (A : SET), Unique (IsSep P A).
Proof.
 intros P A.
 unfold Unique.
 split.
 -
  apply SepAx.
 -
  intros x y H.
  apply ExtenAx.
  intro z.
  destruct H as [Hx Hy].
  apply iff_stepl with (P z /\ In z A).
  +
   unfold IsSep in Hy.
   apply iff_sym.
   apply Hy.
  +
   unfold IsSep in Hx.
   apply iff_sym.
   apply Hx.
Qed.
Definition sep (P : SET -> Prop) (A : SET) := Uniqued (IsSep P A) (UniqueSep P A).
Definition SepUx (P : SET -> Prop) (A : SET) := UniqueAx (IsSep P A) (UniqueSep P A).

(* 集合に対する帰納法の公理 *)
Axiom IndAx : forall (P : SET -> Prop),
 (forall a, (forall x, In x a -> P x) -> P a) -> forall a, P a.

(* 値域がIZFの宇宙である多価関数 *)
Definition mf_u (P : SET -> SET -> Prop) (A : SET) := forall x, In x A -> exists y, P x y.
(* 多価関数 *)
Definition mf (P : SET -> SET -> Prop) (A : SET) (B : SET)
 := forall x, In x A -> exists y, In y B /\ P x y.
(* 収集公理 *)
Axiom ColAx : forall (P : SET -> SET -> Prop) a, mf_u P a -> exists b, mf P a b.