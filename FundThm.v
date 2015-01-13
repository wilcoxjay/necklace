
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import SnocList.
Require Import Relations.Relation_Operators.

Require Import JRWTactics.

Set Implicit Arguments.


Class alphabet :=
  {
    k : nat;
    letter : Type;
    default : letter;
    letter_eq_dec : forall (l l' : letter), {l = l'} + {l <> l'};
    sle : letter -> letter -> Prop;
    slt : letter -> letter -> Prop; (* need to restrain this *)
    total_ord : forall (x y : letter), {sle x y} + {~(sle x y)}
    (* reflexivity *)
    (* transitivity *)
  }.


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


Section FundThm.
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

  Inductive wle : word -> word -> Prop :=
    | wle_nil : wle snil snil
    | wle_snoc : forall a a' w w',
                   a = a' ->
                   wle w w' ->
                   wle (w ::: a) ([a'] +++ w').

  Definition lex_smallest (w : word) : Prop :=
    forall w',
      rotation_of w' w ->
      wle w w'.

  Definition necklace (w : word) : Prop := 
    lex_smallest w.

  Definition prenecklace (w : word) : Prop :=
    exists w',
      necklace (w +++ w').

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

  Definition lyndon (w : word) : Prop :=
    necklace w /\ ~(periodic w).

  Lemma lyndon_dec :
    forall w,
      {lyndon w} + {~(lyndon w)}.
  Proof.
    admit.
  Qed.

  Inductive prefix : word -> word -> Prop :=
    | P_refl : forall w, 
                 prefix w w
    | P_snoc : forall w w' a, 
                 prefix w w' ->
                 prefix w (w' ::: a).

  Fixpoint all_prefixes (w : word) : snoclist word :=
    match w with
      | snil => snil
      | snoc w' a => smap (fun l => snoc l a) (all_prefixes w')
    end.

  Definition lyn_prefixes (w : word) : snoclist word :=
    sfilter (fun p => if (lyndon_dec p) then true else false) (all_prefixes w).

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


  Theorem fund_thm_of_necklaces :
    forall w n p,
      length w = n - 1 ->
      prenecklace w ->
      p = lyn w ->
      forall b,
        (prenecklace (snoc w b) <-> sle (nth_from_end p w default) b) /\
        (b = nth_from_end p w default -> lyn (snoc w b) = p) /\
        (slt (nth_from_end p w default) b -> lyn (snoc w b) = n).
  Proof.
    admit.
  Qed.

End FundThm.


(*
Section FundThm'.
  Context `{ sigma : alphabet }.

  Definition word := list letter.

  Inductive rotate_by_one : word -> word -> Prop :=
    | RBO_step : forall a w, rotate_by_one (w++[a]) (a :: w).

  Definition rotation_of : word -> word -> Prop :=
    clos_refl_trans word rotate_by_one.

  Lemma rotation_of__same_length :
    forall w w',
      rotation_of w w' ->
      length w = length w'.
  Proof.
    admit.
  Qed.

  Inductive wle : word -> word -> Prop :=
    | wle_nil : wle nil nil
    | wle_cons : forall a a' w w',
                   a = a' ->
                   wle w w' ->
                   wle (a :: w) (a' :: w').

  Definition lex_smallest (w : word) : Prop :=
    forall w',
      rotation_of w' w ->
      wle w w'.

  Definition necklace (w : word) : Prop := 
    lex_smallest w.

  Definition prenecklace (w : word) : Prop :=
    exists w',
      necklace (w ++ w').

  Fixpoint concat (n : nat) (w : word) :=
    match n with
      | O => nil
      | S n' => w ++ (concat n' w)
    end.

  Definition periodic (w : word) : Prop :=
    exists w',
      length w' <= length w /\
      exists n,
        concat n w' = w.

  Definition lyndon (w : word) : Prop :=
    necklace w /\ ~(periodic w).

  Inductive prefix : word -> word -> Prop :=
    | P_refl : forall w, 
                 prefix w w
    | P_snoc : forall w w' a, 
                 prefix w w' ->
                 prefix w (w' ++ [a]).

  Fixpoint all_prefixes (w : word) : list word :=
    let w' = rev w in
    match w' with
      | nil => 


  (* define *set* of lyndon prefixes for a given word,
     then define lyn as the length of the longest one *)

  Definition longest_lyn_prefix (p w : word) : Prop :=
    prefix p w /\
    lyndon p /\
    (forall p',
       prefix p' w ->
       lyndon p' ->
       length p' < length p).

  Definition lyn (w : word) : nat :=
    


(*
Let \alpha = a_1 a_2 ... a_{n-1} \in P_k(n-1) and let p = lyn(\alpha).
The string \alpha b \in P_k(n) iff a_{n-p} \le b \le k-1.  Furthermore,

lyn(\alpha b) = 
  | p     if b = a_{n-p}
  | n     else.
*)



  Definition lyn (w : word) : Prop :=
    
    
  Theorem fundamental_theorem :
    

(*
  Inductive rotation_of {n : nat} : word n -> word n -> Prop :=
    | RO_refl : forall w, 
                  rotation_of w w
    | RO_step : forall {n' : nat} (a : letter) (w' : word n') (w : word (S n')), 
                  rotation_of (append w' [a]) w ->
                  rotation_of (a :: w') w.
*)


End FundThm.




(*
Inductive fin : nat -> Set :=
  | FO : forall {n}, fin (S n)
  | FS : forall {n}, fin n -> fin (S n).

Check (FS (FO)).

Check FO.

Lemma fin_eq_dec :
  forall n (a b : fin n), 
    {a = b} + {a <> b}.
Proof.
  admit.
Qed.



Section FundThm'.

Variable k : nat.

Definition sigma := fin (S k).
Hint Unfold sigma.


Fixpoint fin_to_nat {n : nat} (a : fin n) :=
  match a with
    | FO m => m
    | FS n' a' => fin_to_nat a'
  end.

Definition sle' (a b : sigma) := le (fin_to_nat a) (fin_to_nat b).

(*
Reserved Notation "a '<<==' b" (at level 70).

Inductive sle (a : sigma) : sigma -> Prop :=
  | sle_n : a <<== a
  | sle_S : forall b, a <<== b -> a <<== b

where "a '<<==' b" := (sle a b).
*)

Print le.

(*
Inductive sle'' {n : nat} (a : fin n) : fin n -> Prop :=
  | sle_a : sle'' a a
  | sle_S : forall b, sle'' a b -> sle'' a (FS b)
*)

Inductive sle'' : forall n, fin (S n) -> fin (S n) -> Prop :=
  | sle_O : forall n b, sle'' n FO b
  | sle_S : forall n a b, sle'' n a b -> sle'' (S n) (FS a) (FS b).




  | sle'_n : forall a, sle' a a
  | 


Fixpoint sleb (n : nat) (a b : fin n) : bool :=
  match a with
    | FO _ => true
    | FS n' a' => match b with
                    | FO _ => false
                    | FS n' b' => sleb n' a' b'
                  end
  end.



Definition word (n : nat) := t sigma n. (* t is the vector type constructor *)


End FundThm.  
*)






(* Fundamental Theorem of Necklaces *)

(* 
Let \alpha = a_1 a_2 ... a_{n-1} \in P_k(n-1) and let p = lyn(\alpha).
The string \alpha b \in P_k(n) iff a_{n-p} \le b \le k-1.  Furthermore,

lyn(\alpha b) = 
  | p     if b = a_{n-p}
  | n     else.
*)

*)




