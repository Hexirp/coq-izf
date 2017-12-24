Require Import Init.Prelude.

(** 集合の型 *)
Axiom set : Type.
(** 帰属関係の述語 *)
Axiom elem : set -> set -> Prop.
(** 帰属関係の記法。∈の見立て。 *)
Notation "x ':e' y" := (elem x y) (at level 70) : type_scope.
(** 帰属関係の否定。∉の見立て。 *)
Notation "x ':/e ' y" := (~ x :e y) (at level 70) : type_scope.
(** 集合により限定された全称量化 *)
Notation "'forall' x ':e' a ',' p"
  := (forall x : set, x :e a -> p) (at level 199, x ident, right associativity) : type_scope.
(** 集合により限定された存在量化 *)
Notation "'exists' x ':e' a ',' p"
  := (sigT set (fun x => x :e a * p)) (at level 199, x ident, right associativity) : type_scope.

(* 包含関係 *)
Definition sub (a b : set) : Prop := forall x, x :e a -> x :e b.
(* 包摂関係の記法。⊂の見立て。 *)
Notation "x 'c=' y" := (sub x y) (at level 70) : type_scope.
Notation "x 'c/=' y" := (~ sub x y) (at level 70) : type_scope.
(* 反射律 *)
Definition sub_refl (a : set) : a c= a := fun _ i => i.
(* 推移律 *)
Definition sub_trans (a b c : set) : a c= b -> b c= c -> a c= c
  := fun f g => fun x i => g x (f x i).

(* 外延 *)
Definition exten (a b : set) : Prop := forall x, x :e a <-> x :e b.
Notation "x '~' y" := (exten x y) (at level 95, no associativity) : type_scope.
(* 反射律 *)
Definition exten_refl (a : set) : a ~ a := fun _ => (fun i => i, fun i => i).
(* 対称律 *)
Definition exten_sym (a b : set) : a ~ b -> b ~ a :=
 fun H => fun x => match H x with
 | (f, g) => (g, f)
 end
.
(* 推移律 *)
Definition exten_trans (a b c : set) : a ~ b -> b ~ c -> a ~ c.
Proof.
 refine (fun H I => _).
 refine (fun x => (_, _)).
