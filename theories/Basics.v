Local Unset Elimination Schemes.

Inductive list_in (A : Type) (a : A) : list A -> Type :=
| ino : forall x, list_in A a (cons a x)
| ins : forall x b, list_in A a x -> list_in A a (cons b x)
.

Scheme list_in_ind := Induction for list_in Sort Type.
Scheme list_in_rec := Minimality for list_in Sort Type.
Definition list_in_rect := list_in_ind.

Inductive paths (A : Type) (a : A) : A -> Type :=
| idpath : paths A a a
.

Scheme paths_ind := Induction for paths Sort Type.
Scheme paths_rec := Minimality for paths Sort Type.
Definition paths_rect := paths_ind.

Inductive iff (A B : Type) :=
| prod_iff : (A -> B) -> (B -> A) -> iff A B
.

Scheme iff_ind := Induction for iff Sort Type.
Scheme iff_rec := Minimality for iff Sort Type.
Definition iff_rect := iff_ind.

Section set.
 Axiom set : Type -> Type.
 Axiom set_of : forall a, list a -> set a.
 Axiom set_exten
  : forall A,
   forall (a b : list A),
    (forall x, iff (list_in A x a) (list_in A x b)) ->
     paths (set A) (set_of A a) (set_of A b).

 Definition example : paths (set nat)
  (set_of nat (0 :: 1 :: nil)%list)
  (set_of nat (1 :: 0 :: nil)%list).
 Proof.
  apply set_exten.
  intros x.
  apply prod_iff.
  -
   intros H.
   inversion H.
   +
    apply ins.
    apply ino.
   +
    inversion H1.
    *
     apply ino.
    *
     inversion H4.
  -
   intros H.
   inversion H.
   +
    apply ins.
    apply ino.
   +
    inversion H1.
    *
     apply ino.
    *
     inversion H4.
 Defined.

 Print example.