Require Import Init.

(** 集合の型 *)
Axiom SET : Type.
(** 帰属関係の述語 *)
Axiom In : SET -> SET -> Prop.
(** 帰属関係の記法。∈の見立て。 *)
Notation "x ':e' y" := (In x y) (at level 70).
(** 帰属関係の否定。∉の見立て。 *)
Notation "x ':/e ' y" := (~ In x y) (at level 70).

(** ある集合の元すべてに対する量化 *)
Notation "forall x :e a , p" := (forall x : SET, x :e a -> p) (at level 200, x ident).
(** ある集合の元のうちいくつかの元に対する量化 *)
Notation "exists x :e a , p" := (exists x : SET, x :e a /\ p) (at level 200, x ident).
 
(* 包含関係 *)
Definition Sub (A : SET) (B : SET) := forall x, x :e A -> x :e B.
(* 包摂関係の記法。⊂の見立て。 *)
Notation "x 'c=' y" := (Sub x y) (at level 70).