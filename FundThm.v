
Require Import Program.
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import SnocList.
Require Import Relations.

Require Import JRWTactics.

Set Implicit Arguments.


Inductive fin : nat -> Set :=
  | FO : forall n, fin (S n)
  | FS : forall n, fin n -> fin (S n).

Check (FS (FO 4)).

Check (FS (FS (FO 3))).

Check FO.

Lemma fin_eq_dec :
  forall n (a b : fin n), 
    {a = b} + {a <> b}.
Proof.
  admit.
Qed.


Class alphabet :=
  {
    k : nat;
    letter : Type;
    default : letter;
    letter_eq_dec : forall (l l' : letter), {l = l'} + {l <> l'};
    ale : letter -> letter -> Prop;
    alt : letter -> letter -> Prop; (* need to restrain this *)
    total_ord : forall (x y : letter), {ale x y} + {~(ale x y)}
    (* reflexivity *)
    (* transitivity *)
    (* bijection between letters and fin types *)
  }.


Section Word.
  Context `{ sigma : alphabet }.

  Definition word := snoclist letter.

  Inductive rotate_by_one : word -> word -> Prop :=
    | RBO_step : forall (a : letter) (w : snoclist letter),
                   rotate_by_one (snoc w a) ([a] +++ w).

  Definition rotation_of : word -> word -> Prop :=
    clos_refl_trans word rotate_by_one.
  
  Lemma rotation_of__same_length :
    forall w w',
      rotation_of w w' ->
      length w = length w'.
  Proof.
    admit.
  Qed.

  Inductive wlt : word -> word -> Prop :=
    | wlt_snil : forall a w,
                   wlt snil (snoc w a)
    | wlt_alt  : forall a a' w w',
                   alt a a' ->
                   wlt ([a] +++ w) ([a'] +++ w')
    | wlt_aeq  : forall a a' w w',
                   a = a' ->
                   wlt w w' ->
                   wlt ([a] +++ w) ([a'] +++ w').

  Definition wle (w w' : word) : Prop :=
    (w = w') \/ (wlt w w').

  Inductive prefix : word -> word -> Prop :=
    | P_refl : forall w, 
                 prefix w w
    | P_snoc : forall w w' a, 
                 prefix w w' ->
                 prefix w (w' ::: a).

  Fixpoint all_prefixes (w : word) : snoclist word :=
    match w with
      | snil      => [snil]
      | snoc w' a => snoc (all_prefixes w') w
    end.

  Fixpoint concat_n (n : nat) (w : word) :=
    match n with
      | O => snil
      | S n' => w +++ (concat_n n' w)
    end.

  Definition periodic (w : word) : Prop :=
    exists w',
      length w' < length w /\
      exists n,
        concat_n n w' = w.

End Word.


Section FundThm.
  Context `{ sigma : alphabet }.
  
  Definition necklace (w : word) : Prop :=
    forall w',
      rotation_of w' w ->
      wle w w'.

  Definition prenecklace (w : word) : Prop :=
    exists w',
      necklace (w +++ w').

  Definition lyndon (w : word) : Prop :=
    necklace w /\ ~(periodic w).

  Hint Unfold necklace.
  Hint Unfold prenecklace.
  Hint Unfold lyndon.

  Lemma lyndon_dec :
    forall w,
      {lyndon w} + {~(lyndon w)}.
  Proof.
    admit.
  Qed.

  (* lyn prefixes are ordered from smallest to largest *)
  Definition lyn_prefixes (w : word) : snoclist word :=
    sfilter (fun p => if (lyndon_dec p) then true else false) (all_prefixes w).

  (* lyn takes size of last element of lyn_prefixes *)
  Definition lyn (w : word) : nat :=
    match lyn_prefixes w with
      | snil => 0
      | l:::a => length a
    end.

  Lemma concat_n_necklace :
    forall w n,
      necklace w ->
      1 <= n ->
      necklace (concat_n n w).
  Proof.
    admit.
  Qed.

  Lemma prenecklace_characterization_1 :
    forall w,
      prenecklace w <->
      (forall i,
         i <= length w ->
         wle (first_n i w) (last_n i w)).
  Proof.
    admit.
  Qed.

  Lemma prenecklace_characterization_2 : 
    forall w i,
      i <= length w ->
      i > lyn w ->
      nth default i w = nth default (i - lyn w) w.
  Proof.
    admit.
  Qed.

  Lemma lyndon_characterization :
    forall w,
      lyndon w <->
      (forall x y,
         w = x+++y ->
         wlt (y+++x) w).
  Proof.
    admit.
  Qed.

  Lemma next_lyn : 
    forall w a,
      lyn (snoc w a) = lyn w \/ lyn (snoc w a) = length w + 1.
  Proof.
    admit.
  Qed.

  Theorem fund_thm_of_necklaces :
    forall w p,
      prenecklace w ->
      p = lyn w ->
      forall b,
        (prenecklace (snoc w b) <-> ale (nth_from_end default p w) b) /\
        (b = nth_from_end default p w -> lyn (snoc w b) = p) /\
        (alt (nth_from_end default p w) b -> lyn (snoc w b) = length w + 1).
  Proof.
    admit.
  Qed.

  

(*
To Do:

- define necklace
  - use fin as alphabet
  - take parameter indicates alphabet size
  - define word
  - define lexicographically smallest property
    - define cyclic rotation of word
  - define necklace : lexicographically smallest word
  - define prenecklace : prefix of some necklace
  - define lyndon word : aperiodic necklace
    - define periodicity
    - define aperiodicity
  - define lyn function

*)





