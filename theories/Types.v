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
Notation "x '~' y" := (exten x y) (at level 70, no associativity) : type_scope.
(* 反射律 *)
Definition exten_refl (a : set) : a ~ a := fun x => iff_refl (x :e a).
(* 対称律 *)
Definition exten_sym (a b : set) : a ~ b -> b ~ a := fun H x => iff_sym (H x).
(* 推移律 *)
Definition exten_trans (a b c : set) : a ~ b -> b ~ c -> a ~ c
  := fun H I x => iff_trans (H x) (I x).

(* 互いに部分集合である二つの集合は外延である *)
Definition sub_exten (a b : set) : a c= b -> b c= a -> a ~ b := fun H I x => conj (H x) (I x).
(* 外延は包摂関係を導く（左） *)
Definition exten_sub_l (a b : set) : a ~ b -> a c= b := fun H x => proj1 (H x).
(* 外延は包摂関係を導く（右） *)
Definition exten_sub_r (a b : set) : a ~ b -> b c= a := fun H x => proj2 (H x).

(* 弱い内包 *)
Definition wcomp (P : set -> Prop) (a : set) : Prop := forall x, P x -> x :e a.
Definition eq_sub_wcomp (a b : set) : a c= b = wcomp (fun x => x :e a) b := eq_refl.
Definition sub_wcomp (p : set -> Prop) (a b : set) : a c= b -> wcomp p a -> wcomp p b
  := fun H I x => compose (H x) (I x).

(* 内包 *)
Definition comp (P : set -> Prop) (a : set) : Prop := forall x, P x <-> x :e a.
Definition eq_exten_comp (a b : set) : a ~ b = comp (fun x => x :e a) b := eq_refl.
Definition comp_wcomp (p : set -> Prop) (a : set) : comp p a -> wcomp p a
  := fun H x => proj1 (H x).
Definition comp_exten (p : set -> Prop) (a b : set) : comp p a -> comp p b -> a ~ b
  := fun H I x => iff_stepl (I x) (H x).
Definition exten_comp (p : set -> Prop) (a b : set) : a ~ b -> comp p a -> comp p b
  := fun H I x => iff_trans (I x) (H x).

(* 記述公理 *)
Definition unique : Type := forall P : set -> Prop, (exists! x, P x) -> {x : set | P x}.

(* 外延公理 *)
Definition extension : Prop := forall a b, a ~ b -> a = b.

Notation "'{{' x '|' p '}}'" := (ex (wcomp (fun x => p))) (at level 99, x ident).

(* 空集合公理 *)
Definition empty : Prop := {{x | False}}.

(* 単集合公理 *)
Definition singleton (a : set) : Prop := {{x | x = a}}.

(* 和集合公理 *)
Definition union (a : set) : Prop := {{x | x :e a}}.

(* 冪集合公理 *)
Definition power (a : set) : Prop := {{x | x c= a }}.

(* 分出公理 *)
Definition specification (P : set -> Prop) (a : set) : Prop := {{x | P x /\ x :e a}}.

(* 帰納法公理 *)
Definition set_ind (P : set -> Prop) : Prop
  := (forall a, (forall x, x :e a -> P x) -> P a) -> forall a, P a.
