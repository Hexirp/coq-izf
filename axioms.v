(* 以下の文献を参考にした。
 * http://shirodanuki.cs.shinshu-u.ac.jp/TPP/TPP2013_satou.pdf （誤字が多いので注意）
 * https://plato.stanford.edu/entries/set-theory-constructive/axioms-CZF-IZF.html
 *)

Require Import Init set.

(* ある述語を満たす集合が一つのみである *)
Definition Unique (P : SET -> Prop) := (exists x, P x) /\ (forall x y, P x /\ P y -> x = y).
(* Pを満たして一意に存在する集合 *)
Axiom Uniqued : forall (P : SET -> Prop), Unique P -> SET.
(* Uniquedの性質の公理 *)
Axiom UniqueAx : forall (P : SET -> Prop) (U : Unique P), P (Uniqued P U).

(* 内包による集合の指定 *)
Definition comp (P : SET -> Prop) (A : SET) := forall x, x :e A <-> P x.

Lemma comp_stepl : forall p a b, comp p a -> comp p b -> forall x, x :e a <-> x :e b.
Proof.
 intros p a b Ha Hb x.
 apply iff_stepl with (p x).
 -
  unfold comp in Hb.
  apply iff_sym.
  apply Hb.
 -
  unfold comp in Ha.
  apply iff_sym.
  apply Ha.
Qed.

(* 外延性の公理 *)
Axiom ExtenAx : forall a b, (forall x, x :e a <-> x :e b) -> a = b.

Lemma comp_exten : forall p a b, comp p a /\ comp p b -> a = b.
Proof.
 intros p a b H.
 destruct H as [Ha Hb].
 apply ExtenAx.
 apply comp_stepl with p.
 -
  apply Ha.
 -
  apply Hb.
Qed.

Lemma comp_unique : forall p, (exists a, comp p a) -> Unique (comp p).
Proof.
 intros p H.
 unfold Unique.
 split.
 -
  apply H.
 -
  apply comp_exten.
Qed.

(* 空集合である *)
Definition IsEmpty := comp (fun _ => False).
(* 空集合の公理 *)
Axiom EmptyAx : exists e, IsEmpty e.
(* 空集合の一意存在性 *)
Theorem UniqueEmpty : Unique IsEmpty.
Proof.
 apply comp_unique.
 apply EmptyAx.
Qed.
(* 空集合 *)
Definition empty := Uniqued IsEmpty UniqueEmpty.
(* 空集合の単一性 *)
Definition EmptyUx := UniqueAx IsEmpty UniqueEmpty.

Definition IsPair (A : SET) (B : SET) := comp (fun x => x = A \/ x = B).
(* 対の公理 *)
Axiom PairAx : forall a b, exists c, IsPair a b c.
Theorem UniquePair : forall (A : SET) (B : SET), Unique (IsPair A B).
Proof.
 intros A B.
 apply comp_unique.
 apply PairAx.
Qed.
Definition pair (A : SET) (B : SET) := Uniqued (IsPair A B) (UniquePair A B).
Definition singleton (A : SET) := pair A A.
Definition PairUx (A : SET) (B : SET) := UniqueAx (IsPair A B) (UniquePair A B).

Definition IsUnion (A : SET) := comp (fun x => exists u, u :e A /\ x :e u).
(* 和集合公理 *)
Axiom UnionAx : forall a, exists b, IsUnion a b.
Theorem UniqueUnion : forall (A : SET), Unique (IsUnion A).
Proof.
 intros A.
 apply comp_unique.
 apply UnionAx.
Qed.
Definition union (A : SET) := Uniqued (IsUnion A) (UniqueUnion A).
Definition union2 (A : SET) (B : SET) := union (pair A B).
Definition UnionUx (A : SET) := UniqueAx (IsUnion A) (UniqueUnion A).
Definition Union2Ux (A : SET) (B : SET) := UnionUx (pair A B).

Definition IsPower (A : SET) := comp (fun x => x c= A).
(* 冪集合公理 *)
Axiom PowerAx : forall a, exists b, IsPower a b.
Theorem UniquePower : forall (A : SET), Unique (IsPower A).
Proof.
 intros A.
 apply comp_unique.
 apply PowerAx.
Qed.
Definition power (A : SET) := Uniqued (IsPower A) (UniquePower A).
Definition PowerUx (A : SET) := UniqueAx (IsPower A) (UniquePower A).

(* 後者関数 *)
Definition succ (A : SET) := union2 A (singleton A).
Definition IsInf (A : SET) := In empty A /\ (forall n, In n A -> succ n :e A).
(* 無限公理 *)
Axiom InfAx : exists a, IsInf a.

Definition IsSep (P : SET -> Prop) (A : SET) := comp (fun x => P x /\ x :e A).
(* 分出公理 *)
Axiom SepAx : forall p a, exists b, IsSep p a b.
Theorem UniqueSep : forall (P : SET -> Prop) (A : SET), Unique (IsSep P A).
Proof.
 intros P A.
 apply comp_unique.
 apply SepAx.
Qed.
Definition sep (P : SET -> Prop) (A : SET) := Uniqued (IsSep P A) (UniqueSep P A).
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