Require Import Init.Prelude.

Definition compose {A B C : Type} : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

(** 集合の型 *)
Axiom set : Type.
(** 帰属関係の述語 *)
Axiom elem : set -> set -> Prop.
(** 帰属関係の記法。∈の見立て。 *)
Notation "x ':e' y" := (elem x y) (at level 70) : type_scope.
(** 帰属関係の否定。∉の見立て。 *)
Notation "x ':/e' y" := (~ x :e y) (at level 70) : type_scope.
(** 集合により限定された全称量化 *)
Notation "'forall' x ':e' a ',' p"
  := (forall x, x :e a -> p) (at level 199, x ident, right associativity) : type_scope.
(** 集合により限定された存在量化 *)
Notation "'exists' x ':e' a ',' p"
  := (exists x, x :e a /\ p) (at level 199, x ident, right associativity) : type_scope.

(* 包含関係 *)
Definition sub (a b : set) : Prop := forall x, x :e a -> x :e b.
(* 包摂関係の記法。⊂の見立て。 *)
Notation "x 'c=' y" := (sub x y) (at level 70) : type_scope.
Notation "x 'c/=' y" := (~ sub x y) (at level 70) : type_scope.
(* 反射律 *)
Definition sub_refl (a : set) : a c= a := fun (x : set) => @idProp (x :e a).
(* 推移律 *)
Definition sub_trans (a b c : set) : b c= c -> a c= b -> a c= c
  := fun f g (x : set) => compose (f x) (g x).

(* 外延 *)
Definition exten (a b : set) : Prop := forall x, x :e a <-> x :e b.
Notation "x '~' y" := (exten x y) (at level 95, no associativity) : type_scope.
(* 反射律 *)
Definition exten_refl (a : set) : a ~ a := fun x => iff_refl (x :e a).
(* 対称律 *)
Definition exten_sym (a b : set) : a ~ b -> b ~ a := fun H x => iff_sym (H x).
(* 推移律 *)
Definition exten_trans (a b c : set) : a ~ b -> b ~ c -> a ~ c := fun H I x => iff_trans (H x) (I x).

(* 互いに部分集合である二つの集合は外延である *)
Definition sub_exten (a b : set) : a c= b -> b c= a -> a ~ b := fun H I x => conj (H x) (I x).
(* 外延は包摂関係を導く（左） *)
Definition exten_sub_l (a b : set) : a ~ b -> a c= b := fun H x => proj1 (H x).
(* 外延は包摂関係を導く（右） *)
Definition exten_sub_r (a b : set) : a ~ b -> b c= a := fun H x => proj2 (H x).

(* 弱い内包 *)
Definition wcomp (P : set -> Prop) (a : set) := forall x, P x -> x :e a.
Notation "x '<e' p" := (wcomp p x) (at level 70) : type_scope.
Definition sub_wcomp (a b : set) : (a c= b) = (wcomp (fun x => x :e a) b) := eq_refl.
