Require Import Le Gt Minus Bool Setoid.

Set Implicit Arguments.


Inductive snoclist (A : Type) : Type :=
  | snil : snoclist A
  | snoc : snoclist A -> A -> snoclist A.

Arguments snil {A}.
Arguments snoc {A} _ _.  (* use underscore for argument position that has no name *)

Fixpoint app {A : Type} (l1 l2 : snoclist A) : (snoclist A) :=
  match l2 with
  | snil       => l1
  | snoc l2' x => snoc (app l1 l2') x
  end.

Fixpoint length {A : Type} (l : snoclist A) : nat :=
  match l with
    | snil      => 0
    | snoc l' x => 1 + length l'
  end.

Notation "l ::: x" := (snoc l x)
                     (at level 61, left associativity).
Notation "[ ]" := snil.
Notation "[ x ]" := (snoc snil x).
Notation "[ x ; .. ; y ]" := (snoc .. (snoc snil x) .. y).
Notation "x +++ y" := (app x y)
                     (at level 61, left associativity).


Section Map.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint smap (l : snoclist A) : snoclist B :=
    match l with
      | snil => snil
      | l':::a => snoc (smap l') (f a)
    end.
End Map.


Section Bool.
  Variable A : Type.
  Variable f : A -> bool.

  Fixpoint sfilter (l : snoclist A) : snoclist A :=
    match l with
      | snil => snil
      | l':::x => if f x then (sfilter l'):::x else sfilter l'
    end.
End Bool.


Section Elmts.

  Variable A : Type.

  Fixpoint nth_from_end (n : nat) (l : snoclist A) (default : A) : A :=
    match n, l with
      | O, l':::x => x
      | S n', l':::x => nth_from_end n' l' default
      | _, [] => default
    end.

End Elmts.


