Require Import Init.

Require Import Types Comprehension.

(* 空集合である *)
Definition IsEmpty := comp (fun _ => False).
(* 空集合の公理 *)
Axiom EmptyAx : exists e, IsEmpty e.