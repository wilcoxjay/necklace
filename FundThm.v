
Require Import Program.
Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Relations.

Require Import JRWTactics.

Require Import Omega.

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
    letter : Set;
    default : letter;
    letter_eq_dec : forall (l l' : letter), {l = l'} + {l <> l'};
    ale : letter -> letter -> Prop;
    alt : letter -> letter -> Prop; (* need to restrain this *)
    total_ord : forall (x y : letter), {ale x y} + {~(ale x y)};
    alt_dec : forall (x y : letter), {alt x y} + {~(alt x y)};
    trichotomy : forall x y, {alt x y} + {x = y} + {alt y x}

    (* reflexivity *)
    (* transitivity *)
    (* bijection between letters and fin types *)
  }.


Section Word.
  Context `{ sigma : alphabet }.

  Definition word := list letter.

  Fixpoint rot {A} (n : nat) (l : list A) : list A :=
    match n with
      | 0 => l
      | S n' => rot n' (match l with
                          | [] => []
                          | x :: l' => l' ++ [x]
                        end)
    end.

  Lemma length_rot :
    forall A n w,
      length (rot (A:=A) n w) = length w.
  Proof.
    induction n; intros; simpl; auto.
    destruct w; auto.
    simpl. rewrite IHn. rewrite app_length. simpl. omega.
  Qed.

  Lemma rot_nil :
    forall A n,
      rot (A:=A) n [] = [].
  Proof.
    induction n; auto.
  Qed.

  Lemma skipn_app_1 :
    forall n A x y,
      n <= length x ->
      skipn (A:=A) n (x ++ y) = skipn n x ++ y.
  Proof.
    induction n; intros; simpl in *; auto.
    destruct x; simpl in *.
    - omega.
    - rewrite IHn by omega. auto.
  Qed.

  Lemma firstn_app_1 :
    forall n A x y,
      n <= length x ->
      firstn (A:=A) n (x ++ y) = firstn n x.
  Proof.
    induction n; intros; simpl in *.
    - auto.
    - destruct x; simpl in *.
      + omega.
      + rewrite IHn by omega. auto.
  Qed.

  Lemma rot_firstn_skipn :
    forall A n w,
      n <= length w ->
      rot (A:=A) n w = skipn n w ++ firstn n w.
  Proof.
    induction n; intros; simpl.
    - rewrite app_nil_r. auto.
    - break_match.
      + apply rot_nil.
      + subst. simpl in *. rewrite IHn by (rewrite app_length; simpl; omega).
        rewrite skipn_app_1 by omega.
        rewrite firstn_app_1 by omega.
        rewrite app_ass. auto.
  Qed.

  Lemma skipn_length :
    forall A x,
      skipn (A:=A) (length x) x = [].
  Proof.
    induction x; intros; simpl; auto.
  Qed.

  Lemma firstn_length :
    forall A x,
      firstn (A:=A) (length x) x = x.
  Proof.
    induction x; intros; simpl; auto using f_equal.
  Qed.

  Lemma rot_length :
    forall A w,
      rot (A:=A) (length w) w = w.
  Proof.
    intros.
    rewrite rot_firstn_skipn by omega.
    rewrite skipn_length.
    rewrite firstn_length. auto.
  Qed.

  Lemma rot_plus :
    forall n m A w,
      rot (A:=A) (n + m) w = rot m (rot n w).
  Proof.
    induction n; intros; simpl; auto.
  Qed.

  Require Import NPeano.

  Lemma rot_length_mult :
    forall A w n,
      rot (A:=A) (length w * n) w = w.
  Proof.
    intros.
    rewrite mult_comm.
    induction n; simpl; auto.
    rewrite rot_plus.
    rewrite rot_length. auto.
  Qed.

  Lemma rot_mod :
    forall A n w,
      rot (A:=A) n w = rot (n mod (length w)) w.
  Proof.
    intros.
    destruct w.
    - simpl. now rewrite rot_nil.
    - pose proof Nat.div_mod n (length (a :: w)).
      conclude_using ltac:(destruct w; try congruence; simpl; omega).
      rewrite H at 1.
      rewrite rot_plus.
      rewrite rot_length_mult. auto.
  Qed.

  Definition rotation_of {A} w w' := exists n, rot (A:=A) n w = w'.

  Lemma rotation_of_elim :
    forall A w w',
      rotation_of (A:=A) w w' ->
      exists n,
        n <= length w /\
        rot n w = w'.
  Proof.
    unfold rotation_of.
    intros.
    break_exists.
    exists (x mod (length w)). split.
    + destruct w.
      * simpl. auto.
      * apply lt_le_weak. apply Nat.mod_upper_bound. discriminate.
    + now rewrite <- rot_mod.
  Qed.

  Definition wlt : word -> word -> Prop := @Ltl letter alt.

  Section Ltl.
    Variable A : Set.
    Variable ltA : A -> A -> Prop.
    Hypotheses not_ltA_leA : forall x y, (~ ltA x y) -> {ltA y x} + {x = y}.
    Hypotheses ltA_neq : forall x y, ltA x y -> x <> y.
    Hypothesis ltA_dec : forall x y : A, {ltA x y} + {~ltA x y}.

    Lemma Ltl_dec : forall xs ys : list A, {Ltl A ltA xs ys} + {~Ltl A ltA xs ys}.
      induction xs; intros.
      - destruct ys.
        + right. intro. inversion H.
        + left. constructor.
      - destruct ys.
        + right. intro. inversion H.
        + destruct (ltA_dec a a0).
          * left. constructor. auto.
          * copy_apply not_ltA_leA n.
            {
              destruct H.
              - right. intro. invc H; congruence.
              - subst. destruct (IHxs ys).
                + auto using Lt_tl.
                + right. intro. invc H; congruence.
            }
    Qed.
  End Ltl.

  Definition wle (w w' : word) : Prop :=
    (w = w') \/ (wlt w w').

  Definition wlt_dec (w w' : word) : {wlt w w'} + {~wlt w w'}.
    apply Ltl_dec.
    - intros. destruct (trichotomy x y); intuition.
    - apply alt_dec.
  Defined.

  Definition weq_dec (w w' : word) : {w = w'} + {w <> w'}.
    apply list_eq_dec.
    apply letter_eq_dec.
  Defined.

  Definition wle_dec (w w' : word) : {wle w w'} + {~wle w w'}.
    unfold wle.
    destruct (weq_dec w w'), (wlt_dec w w'); intuition.
  Qed.

  Fixpoint Prefix {A} (xs ys : list A) : Prop :=
    match xs with
      | [] => True
      | x :: xs' => match ys with
                      | [] => False
                      | y :: ys' => x = y /\ Prefix xs' ys'
                    end
    end.

  Fixpoint all_prefixes (w : word) : list word :=
    match w with
      | []     => [[]]
      | a :: w' => [] :: map (fun p => a :: p) (all_prefixes w')
    end.

  Lemma all_prefixes_sound :
    forall w p,
      In p (all_prefixes w) ->
      Prefix p w.
  Proof.
    induction w; intros; simpl in *; intuition; subst; simpl; auto.
    find_apply_lem_hyp in_map_iff. break_exists. intuition. subst.
    simpl. intuition.
  Qed.

  Lemma all_prefixes_complete :
    forall p w,
      Prefix p w ->
      In p (all_prefixes w).
  Proof.
    induction p; intros; destruct w; simpl in *; intuition.
    subst. right.  auto using in_map.
  Qed.

  Fixpoint concat_n {A} (n : nat) (w : list A) :=
    match n with
      | O => []
      | S n' => w ++ (concat_n n' w)
    end.

  Definition periodic (w : word) : Prop :=
    exists w',
      length w' < length w /\
      exists n,
        concat_n n w' = w.

  Lemma Prefix_app :
    forall A xs ys,
      Prefix (A:=A) xs (xs ++ ys).
  Proof.
    induction xs; simpl; intuition.
  Qed.

  Lemma concat_n_prefix :
    forall A n w w',
      n <> 0 ->
      concat_n (A:=A) n w' = w ->
      Prefix w' w.
  Proof.
    destruct n; simpl; intros; try congruence.
    subst.
    auto using Prefix_app.
  Qed.

  Definition is_periodic (w : word) : bool :=
    existsb (fun r => if weq_dec w (concat_n (length w / length r) r)
                      then ltb (length r) (length w)
                      else false)
            (all_prefixes w).

  Lemma is_periodic_sound :
    forall w,
      is_periodic w = true ->
      periodic w.
  Proof.
    unfold periodic, is_periodic.
    intros.
    find_apply_lem_hyp existsb_exists. break_exists. intuition.
    break_if; try discriminate.
    exists x. intuition.
    - apply ltb_lt. auto.
    - eauto.
  Qed.

  Lemma length_concat_n :
    forall A n w,
      length (concat_n (A:=A) n w) = n * length w.
  Proof.
    induction n; intros; simpl.
    - auto.
    - rewrite app_length. rewrite IHn. auto.
  Qed.

  Lemma is_periodic_complete :
    forall w,
      periodic w ->
      is_periodic w = true.
  Proof.
    unfold periodic, is_periodic.
    intros.
    apply existsb_exists.
    break_exists. intuition. break_exists.
    exists x.
    intuition.
    - destruct x0.
      + simpl in *. subst. simpl in *. omega.
      + apply all_prefixes_complete. eapply concat_n_prefix; try eassumption; auto.
    - break_if.
      + apply ltb_lt; auto.
      + subst w. rewrite length_concat_n in *.
        rewrite Nat.div_mul in *. congruence.
        intro. rewrite H in *. rewrite <- mult_n_O in *. omega.
  Qed.

  Definition periodic_dec (w : word) : {periodic w} + {~periodic w}.
    destruct (is_periodic w) eqn:?.
    - auto using is_periodic_sound.
    - right. intro. find_apply_lem_hyp is_periodic_complete. congruence.
  Qed.

  Definition all_rotations (w : word) : list word :=
    match w with
      | [] => [[]]
      | _ => map (fun i => rot i w) (seq 0 (length w))
    end.

  Lemma rotation_of_sym :
    forall A w w',
      rotation_of (A:=A) w w' ->
      rotation_of w' w.
  Proof.
    intros.
    find_apply_lem_hyp rotation_of_elim. break_exists. intuition.
    red.
    exists (length w - x).
    subst w'.
    rewrite <- rot_plus.
    rewrite <- le_plus_minus by auto.
    apply rot_length.
  Qed.

  Lemma seq_bounds :
    forall len n x,
      In x (seq n len) ->
      n <= x < n + len.
  Proof.
    induction len; simpl; intros.
    - intuition.
    - break_or_hyp.
      + omega.
      + apply IHlen in H0. omega.
  Qed.

  Lemma seq_in :
    forall len n x,
      n <= x < n + len ->
      In x (seq n len).
  Proof.
    induction len; intros.
    - omega.
    - simpl. simpl. assert (n = x \/ n < x < n + S len) by omega. intuition.
  Qed.

  Lemma all_rotations_sound :
    forall w r,
      In r (all_rotations w) ->
      rotation_of w r.
  Proof.
    unfold all_rotations.
    intros.
    red.
    break_match.
    - subst. simpl in *. intuition subst. exists 0. auto.
    - find_apply_lem_hyp in_map_iff. break_exists. intuition. subst.
      eauto.
  Qed.

  Lemma all_rotations_complete :
    forall w r,
      rotation_of w r ->
      In r (all_rotations w).
  Proof.
    intros.
    find_apply_lem_hyp rotation_of_elim. break_exists. intuition. subst.
    unfold all_rotations.
    destruct w.
    - simpl. left. now rewrite rot_nil.
    - apply le_lt_or_eq in H0. intuition.
      + apply in_map_iff. eexists. intuition eauto.
        apply seq_in. simpl. intuition.
      + subst. rewrite rot_length.
        apply in_map_iff. exists 0. intuition auto.
        apply seq_in. simpl. omega.
  Qed.

  Lemma rot_is_nil :
    forall A n w,
      rot (A:=A) n w = [] ->
      w = [].
  Proof.
    induction n; simpl; intros.
    - auto.
    - break_match; auto. subst. apply IHn in H. destruct l; discriminate.
  Qed.

  Lemma rotation_of_nil :
    forall A w,
      rotation_of (A:=A) w [] ->
      w = [].
  Proof.
    unfold rotation_of.
    intros.
    break_exists. eauto using rot_is_nil.
  Qed.

  Lemma skipn_app_2 :
    forall n A xs ys,
      length xs <= n ->
      skipn (A:=A) n (xs ++ ys) = skipn (n - length xs) ys.
  Proof.
    induction n; intros; destruct xs; simpl in *; try omega; auto with *.
  Qed.

  Lemma firstn_app_2 :
    forall n A xs ys,
      length xs <= n ->
      firstn (A:=A) n (xs ++ ys) = xs ++ firstn (n - length xs) ys.
  Proof.
    induction n; intros.
    - destruct xs; simpl in *; try omega. auto.
    - simpl. destruct xs; simpl in *.
      + auto.
      + now rewrite IHn by omega.
  Qed.

  Lemma rot_app_1 :
    forall A n xs ys,
      n <= length xs ->
      rot (A:=A) n (xs ++ ys) = skipn n xs ++ ys ++ firstn n xs.
  Proof.
    intros.
    rewrite rot_firstn_skipn by (rewrite app_length; omega).
    rewrite skipn_app_1 by auto.
    rewrite firstn_app_1 by auto.
    auto using app_ass.
  Qed.

  Lemma rot_app_2 :
    forall A n xs ys,
      n <= length ys ->
      rot (A:=A) (length xs + n) (xs ++ ys) = skipn n ys ++ xs ++ firstn n ys.
  Proof.
    intros.
    rewrite rot_firstn_skipn by (rewrite app_length; omega).
    rewrite skipn_app_2 by omega.
    rewrite firstn_app_2 by omega.
    now rewrite minus_plus.
  Qed.

  Lemma mod_double :
    forall a b,
      a mod (2 * b) = a mod b \/
      a mod (2 * b) = (a mod b) + b.
  Proof.
    intros.
    rewrite mult_comm.
    destruct b.
    - auto.
    - rewrite Nat.mod_mul_r by auto.
      pose proof Nat.mod_upper_bound (a/(S b)) 2. concludes.
      destruct ((a/S b) mod 2).
      + omega.
      + destruct n.
        * omega.
        * omega.
  Qed.

  Lemma mod_weak_upper :
    forall a b,
      a mod b <= b.
  Proof.
    destruct b.
    - auto.
    - apply lt_le_weak.
      apply Nat.mod_upper_bound.
      simpl. discriminate.
  Qed.

  (* special case of rot_concat_n_split *)
  Lemma rot_double_split :
    forall n A w,
      rot (A:=A) n (w ++ w) = rot n w ++ rot n w.
  Proof.
    intros.
    intros.
    rewrite rot_mod.
    replace (length (w ++ w)) with (2 * length w) by (rewrite app_length; omega).
    pose proof @mod_double n (length w).

    replace (rot (n mod (2 * length w)) (w ++ w))
    with (skipn (n mod length w) w ++ w ++ firstn (n mod length w) w).
    - rewrite <- firstn_skipn with (n := (n mod length w))(l:=w) at 3.
      repeat rewrite app_ass.
      rewrite <- rot_firstn_skipn by auto using mod_weak_upper.
      rewrite <- app_ass.
      rewrite <- rot_firstn_skipn by auto using mod_weak_upper.
      rewrite <- rot_mod. auto.

    - break_or_hyp.
      + rewrite H0. now rewrite rot_app_1 by auto using mod_weak_upper.
      + rewrite H0. rewrite plus_comm.
        now rewrite rot_app_2 by auto using mod_weak_upper.
  Qed.

  (* special case of rot_concat_n *)
  Lemma rot_double :
    forall A n w,
      rot (A:=A) n (w ++ w) = rot (n mod length w) (w ++ w).
  Proof.
    intros.
    repeat rewrite rot_double_split.
    now rewrite rot_mod.
  Qed.

  Lemma wlt_aeq :
    forall (a : letter) (w w' : word),
      wlt w w' -> wlt (a :: w) (a :: w').
  Proof.
    unfold wlt.
    auto using Lt_tl.
  Qed.

  Lemma wlt_app_1 :
    forall xs ys,
      wlt xs ys ->
      length xs = length ys ->
      forall zs ws,
        wlt (xs ++ zs) (ys ++ ws).
  Proof.
    induction 1; intros.
    - simpl in *. discriminate.
    - simpl. constructor; auto.
    - simpl. apply wlt_aeq. auto.
  Qed.

  Lemma wlt_app_2 :
    forall xs zs ws,
      wlt zs ws ->
      wlt (xs ++ zs) (xs ++ ws).
  Proof.
    induction xs; intros; simpl; auto using wlt_aeq.
  Qed.

  Lemma wle_app :
    forall xs ys zs ws,
      wle xs ys ->
      length xs = length ys ->
      wle zs ws ->
      wle (xs ++ zs) (ys ++ ws).
  Proof.
    unfold wle. intuition idtac; subst; auto using wlt_app_1, wlt_app_2.
  Qed.

  Lemma firstn_concat_n_1 :
    forall A n k w,
      k <= length w ->
      firstn (A:=A) k (concat_n (S n) w) = firstn k w.
  Proof.
    simpl. intros.
    now rewrite firstn_app_1 by auto.
  Qed.

  Lemma concat_n_S :
    forall A n w,
      concat_n (A:=A) (S n) w = w ++ concat_n n w.
  Proof.
    auto.
  Qed.

  Lemma concat_n_S_r :
    forall A n w,
      concat_n (A:=A) (S n) w = concat_n n w ++ w.
  Proof.
    induction n; intros; simpl in *.
    - now rewrite app_nil_r.
    - rewrite app_ass. f_equal. auto.
  Qed.

  Lemma rot_length_concat_n :  forall A n w, rot (A:=A) (length w) (concat_n n w) = concat_n n w.
  Proof.
    induction n; simpl; intros.
    - now rewrite rot_nil.
    - replace (length w) with (length w + 0) by omega.
      rewrite rot_app_2 by omega.
      simpl. rewrite app_nil_r.
      rewrite <- concat_n_S_r. auto.
  Qed.

  Lemma rot_length_concat :
    forall A n m w,
      rot (A:=A) (n * length w) (concat_n m w) = concat_n m w.
  Proof.
    induction n; intros; auto.
    simpl. rewrite rot_plus. rewrite rot_length_concat_n. auto.
  Qed.

  Lemma concat_n_nil :
    forall A n, concat_n (A:=A) n [] = [].
  Proof.
    induction n; auto.
  Qed.

  Lemma rot_concat_n :
    forall A n k w,
      1 <= n ->
      rot (A:=A) k (concat_n n w) = rot (k mod length w) (concat_n n w).
  Proof.
    intros.
    destruct w.
    - simpl. rewrite concat_n_nil. apply rot_nil.
    - destruct k0.
      + simpl. rewrite minus_diag. simpl. auto.
      + remember (S k0) as k'. assert (k' <> 0) by congruence. clear Heqk'.
        rewrite rot_mod.
        rewrite length_concat_n.
        rewrite mult_comm.
        rewrite Nat.mod_mul_r by (simpl; omega).
        rewrite plus_comm.
        rewrite rot_plus.
        rewrite mult_comm.
        now rewrite rot_length_concat.
  Qed.

  Lemma rot_concat_n_split :
    forall A n k w,
      rot (A:=A) k (w ++ concat_n n w) = rot k w ++ rot k (concat_n n w).
  Proof.
    intros.

    destruct n.
    - simpl. rewrite rot_nil. now repeat rewrite app_nil_r.
    - rewrite rot_concat_n by omega.
      rewrite <- concat_n_S.
      rewrite rot_concat_n by omega.
      rewrite rot_mod with (w := w). rewrite concat_n_S.
      rewrite rot_app_1 by auto using mod_weak_upper.
      rewrite rot_firstn_skipn by auto using mod_weak_upper.

      rewrite app_ass. f_equal.

      rewrite rot_firstn_skipn by (simpl; rewrite app_length; eauto using mod_weak_upper with *).
      rewrite firstn_concat_n_1 by auto using mod_weak_upper.

      rewrite <- app_ass. f_equal.

      rewrite <- firstn_concat_n_1 with (n:=n) by auto using mod_weak_upper.
      now rewrite firstn_skipn.
  Qed.
End Word.

Section FundThm.
  Context `{ sigma : alphabet }.
  
  Definition necklace (w : word) : Prop :=
    forall w',
      rotation_of w' w ->
      wle w w'.

  Definition prenecklace (w : word) : Prop :=
    exists w',
      necklace (w ++ w').

  Definition lyndon (w : word) : Prop :=
    necklace w /\ ~(periodic w).

  Hint Unfold necklace.
  Hint Unfold prenecklace.
  Hint Unfold lyndon.

  Definition is_necklace (w : word) : bool :=
    forallb (fun r => if wle_dec w r then true else false) (all_rotations w).

  Lemma is_necklace_sound :
    forall w,
      is_necklace w = true ->
      necklace w.
  Proof.
    unfold is_necklace, necklace.
    intros.
    rewrite forallb_forall in H.
    find_apply_lem_hyp rotation_of_sym.
    find_apply_lem_hyp all_rotations_complete.
    apply H in H0.
    break_if; try discriminate. auto.
  Qed.

  Lemma is_necklace_complete :
    forall w,
      necklace w ->
      is_necklace w = true.
  Proof.
    unfold is_necklace, necklace.
    intros.
    apply forallb_forall. intros.
    find_apply_lem_hyp all_rotations_sound.
    find_apply_lem_hyp rotation_of_sym.
    apply H in H0. break_if; congruence.
  Qed.

  Definition necklace_dec (w : word) : {necklace w} + {~necklace w}.
    destruct (is_necklace w) eqn:?.
    - auto using is_necklace_sound.
    - right. intro. find_apply_lem_hyp is_necklace_complete. congruence.
  Defined.

  Lemma lyndon_dec :
    forall w,
      {lyndon w} + {~(lyndon w)}.
  Proof.
    intros. unfold lyndon.
    destruct (necklace_dec w).
    - destruct (periodic_dec w).
      + intuition.
      + intuition.
    - intuition.
  Qed.

  (* lyn prefixes are ordered from smallest to largest *)
  Definition lyn_prefixes (w : word) : list word :=
    filter (fun p => if (lyndon_dec p) then true else false) (all_prefixes w).

  Eval simpl in all_prefixes [default; default; default].

  (* lyn takes size of last element of lyn_prefixes *)
  Definition lyn (w : word) : nat :=
    last (map (@length _) (lyn_prefixes w)) 0.

  (* here's a special case to warm up *)
  Lemma double_necklace :
    forall w,
      necklace w ->
      necklace (w ++ w).
  Proof.
    unfold necklace.
    intros.
    find_apply_lem_hyp rotation_of_sym.
    find_apply_lem_hyp rotation_of_elim.
    break_exists. intuition.
    rewrite rot_double in *.
    rewrite rot_double_split in *. subst.
    assert (wle w (rot (x mod length w) w)) by (apply H; apply rotation_of_sym; red; eauto).
    apply wle_app; auto.
    now rewrite length_rot.
  Qed.

  Lemma concat_n_necklace :
    forall w n,
      necklace w ->
      1 <= n ->
      necklace (concat_n n w).
  Proof.
    induction n; intros.
    - omega.
    - concludes. destruct n.
      + simpl. now rewrite app_nil_r.
      + concludes. unfold necklace in *. intros.
        find_apply_lem_hyp rotation_of_sym.
        find_apply_lem_hyp rotation_of_elim.
        break_exists. intuition.
        rewrite rot_concat_n in * by auto.
        remember (S n) as n'. clear Heqn'.
        simpl in *.
        rewrite rot_concat_n_split in * by auto using mod_weak_upper.
        subst.
        specialize (IHn (rot (x mod length w) (concat_n n' w))).
        forward IHn.
        {
          apply rotation_of_sym.
          red. eauto.
        }
        concludes.
        apply wle_app; auto.
        * eapply H. apply rotation_of_sym. red. eauto.
        * now rewrite length_rot.
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





