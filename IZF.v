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
Axiom ExtenAx : forall a b, (forall x, iff (In x a) (In x b)) -> a = b.

(* 空集合の公理 *)
Axiom EmptyAx : exists e, forall x, not (In x e).
(* 空集合である *)
Definition IsEmpty (A : SET) := forall x, not (In x A).
(* 空集合の一意存在性 *)
Theorem UniqueEmpty : Unique IsEmpty.
Proof.
 unfold Unique.
 split.
 - (* 空集合の存在性 *)
  unfold IsEmpty.
  apply EmptyAx.
 - (* 空集合の一意性 *)
  unfold IsEmpty.
  intros A B H.
  destruct H as [ H1 H2 ].
  apply ExtenAx.
  split.
  + (* 右への含意 *)
   intro H.
   apply H1 in H as Fal.
   destruct Fal.
  + (* 左への含意 *)
   intro H.
   apply H2 in H as Fal.
   destruct Fal.
Qed.
(* 空集合 *)
Definition empty := Uniqued IsEmpty UniqueEmpty.

(* 対の公理 *)
Axiom PairAx : forall a b, exists c, forall x, iff (In x c) (x = a \/ x = b).
Axiom pair : SET -> SET -> SET.
Definition singleton (A : SET) := pair A A.

(* 和集合公理 *)
Axiom UnionAx : forall a, exists b, forall x, iff (In x b) (exists u, In u a /\ In u x).
Definition IsUnion (A : SET) (B : SET) := forall x, iff (In x B) (exists u, In u A /\ In u x).
Theorem UniqueUnion : forall (A : SET), Unique (IsUnion A).
Proof.
 intro A.
 unfold Unique.
 split.
 - (* *)
  unfold IsUnion.
  apply UnionAx.
 - (* *)
  intros x y H.
  destruct H as [ H1 H2 ].
  apply ExtenAx.
  intro x0.
  split.
  + (* *)
   intro H.
   unfold IsUnion in H1.
   unfold IsUnion in H2.
   destruct H1 with x0 as [ I1 I2 ].
   destruct H2 with x0 as [ J1 J2 ].
   apply J2.
   apply I1.
   assumption.
  + (* *)
   intro H.
   unfold IsUnion in H1.
   unfold IsUnion in H2.
   destruct H1 with x0 as [ I1 I2 ].
   destruct H2 with x0 as [ J1 J2 ].
   apply I2.
   apply J1.
   assumption.
Qed.
Definition union (A : SET) := Uniqued (IsUnion A) (UniqueUnion A).
Definition union2 (A : SET) (B : SET) := union (pair A B).

(* 冪集合公理 *)
Axiom PowerAx : forall a, exists b, forall x, iff (In x b) (Sub x a).

(* 後者関数 *)
Definition succ (A : SET) := union2 A (singleton A).
(* 無限公理 *)
Axiom InfAx : exists o,
 In empty o /\ (forall n, In n o -> In (succ n) o).