Require Import Init.Prelude.

(** 集合の型 *)
Axiom set : Type.
(** 帰属関係の述語 *)
Axiom elem : set -> set -> Type.
(** 帰属関係の記法。∈の見立て。 *)
Notation "x ':e' y" := (elem x y) (at level 70).
(** 帰属関係の否定。∉の見立て。 *)
Notation "x ':/e ' y" := (~ x :e y) (at level 70).
(** 集合により限定された全称量化 *)
Notation "'forall' x ':e' a ',' p"
  := (forall x : set, x :e a -> p) (at level 199, x ident, right associativity) : type_scope.
(** 集合により限定された存在量化 *)
Notation "'exists' x ':e' a ',' p"
  := (sigT set (fun x => x :e a * p)) (at level 199, x ident, right associativity) : type_scope.

(* 包含関係 *)
Definition sub (a b : set) : Type := forall x, x :e a -> x :e b.
(* 包摂関係の記法。⊂の見立て。 *)
Notation "x 'c=' y" := (sub x y) (at level 70) : type_scope.
Notation "x 'c/=' y" := (~ sub x y) (at level 70) : type_scope.

(* 反射律 *)
Definition sub_refl (a : set) : sub a a := fun _ x => x.
(* 推移律 *)
Definition sub_trans (a b c : set) : sub a b -> sub b c -> sub a c := fun f g => fun _ x => g _ (f _ x).