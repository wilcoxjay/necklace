Require Import Le Gt Minus Bool Setoid.
Require Import Program.

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


Fixpoint rev {A : Type} (l : snoclist A) : snoclist A :=
  match l with
    | snil => snil
    | snoc l' a => [a] +++ (rev l')
  end.


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

  Fixpoint nth_from_end (default : A) (n : nat) (l : snoclist A) : A :=
    match n, l with
      | O, l':::x    => x
      | S n', l':::x => nth_from_end default n' l'
      | _, []        => default
    end.

  Definition nth default n := (compose (nth_from_end default n) rev).

  Fixpoint last_n (n : nat) (l : snoclist A) : snoclist A :=
    match n, l with
      | 0, _ => snil
      | _, snil => snil
      | S n', snoc l' a => snoc (last_n n' l') a
    end.
  
  Definition first_n n := (compose rev (compose (last_n n) rev)).

End Elmts.


