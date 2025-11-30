Set Warnings "-notation-overridden".
From LF Require Export Logic.

(* Inductively Defined Propositions *)

(* Example: The Collatz Conjecture *)
Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.
Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).
Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) : even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(* Example: Binary relation for comparing numbers *)
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

(* Example: Transitive Closure *)
Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.
Inductive Person : Type := Sage | Cleo | Ridley | Moss.
Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.
Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.
Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

Check @t_trans.
Check @t_step.

(* Example: Reflexive and Transitive Closure *)
Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Definition cs (n m : nat) : Prop := csf n = m.
Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(* Exercise: 1 star, standard, optional (clos_refl_trans_sym) *)
Inductive clos_refl_trans_sym {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step' (x y : X) :
      R x y ->
      clos_refl_trans_sym R x y
  | rt_refl' (x : X) :
      clos_refl_trans_sym R x x
  | rt_trans' (x y z : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y z ->
      clos_refl_trans_sym R x z
  | rt_sym (x y : X) :
      R x y ->
      clos_refl_trans_sym R y x.

(* Example: Permutations *)
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.
(* Exercise: 1 star, standard, optional (perm) *)
Example perm : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with (l2:=[1;3;2]).
  apply perm3_swap23.
  apply perm3_swap23.
Qed.

(* Example: Evenness (yet again) *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "wrong_ev" must have "n" as 1st
        argument in "wrong_ev 0". *)
Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).
Module EvPlayground.
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).
End EvPlayground.
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn. apply ev_SS. apply ev_SS. apply Hn.
Qed.
(* Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. simpl. induction n.
  + apply ev_0.
  + simpl. apply ev_SS. apply IHn.
Qed.

(* Constructing Evidence for Permutations *)
Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.
Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.
(* Exercise: 1 star, standard (Perm3) *)
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2:=[2;1;3]).
  + apply perm3_swap12.
  + apply perm3_swap23.
Qed.
Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a b c.
  apply perm3_trans with (l2:=[a;c;b]).
  + apply perm3_swap23.
  + apply perm3_swap23.
Qed.

Module Ev3.
(* Example: Evenness(yet again) *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
(**
  0 in the type of ev_0 and S (S n) in the type of ev_SS
*)
Inductive list (X : Type) : Type :=
  | nil                         : list X
  | cons (x : X) (l : list X)   : list X.

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H : wrong_ev n) : wrong_ev (S (S n)).

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).
End Ev3.

Module Ev_Playground.
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(* Exercise: ev_double *)
Theorem ev_double : forall n, ev (double n).
Proof.
  intros n.
  simpl.
  induction n as [| n IHn].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
End Ev_Playground.

(* Contructing Evidence for Permutations *)
Lemma Perm3_rev_3 : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.
Lemma Perm3_rev_4 : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

(* Using Evidence in Proofs *)
Theorem ev_inversion : forall (n : nat),
  ev n ->
  (n = 0) \/ (exists n', n = (S (S n')) /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(* Exercise: 1 star, standard (le_inversion) *)
Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m E.
  destruct E as [| n' m' E'].
  - left. reflexivity.
  - right. exists m'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Hnn'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

(* Exercise: 1 star, standard (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Hnn'].
  apply evSS_ev'. apply E'.
Qed.

(* Exercise: 1 star, standard (ev5_nonsense) *)
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H as [| n H1 H2].
  inversion H1 as [| n' H3 H4].
  inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E' *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.
  generalize dependent E'.
Abort.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(* Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' Hn' IHn'].
  - simpl. apply Hm.
  - assert (H: S (S n') + m = S (S (n' + m))).
    { simpl. reflexivity. }
    rewrite H. apply ev_SS. apply IHn'.
Qed.

(* Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m Hnm Hn.
  induction Hn as [| n' Hn' IHn'].
  - simpl in Hnm. apply Hnm.
  - assert (H: S (S n') + m = S (S (n' + m))).
    { simpl. reflexivity. }
    rewrite H in Hnm. apply evSS_ev in Hnm.
    apply IHn'. apply Hnm.
Qed.

(* Exercise: 3 stars, standard, optional (ev_plus_plus) *)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_ev__ev with (n:=(n + n)).
  - simpl.
    assert (H: n + n + (m + p) = (n + m) + (n + p)).
    { apply PeanoNat.Nat.add_shuffle1. }
    rewrite H. apply ev_sum. apply Hnm. apply Hnp.
  - simpl.
    rewrite <- double_plus. apply ev_double.
Qed.

(* Exercise: 4 stars, advanced, optional (ev'_ev) *)
Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).
Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intros H. induction H as [].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros H. induction H as [].
    + apply ev'_0.
    + assert (H' : S (S n) = 2 + n).
      { simpl. reflexivity. }
      rewrite H'.
      apply ev'_sum.
      apply ev'_2.
      apply IHev.
Qed.

Module Perm3Reminder.
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.
End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

(* Exercise: 2 stars, standard (Perm3_In) *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 E.
  induction E as [a b c|a b c|l1 l2 l3 E12 IH12 E23 IH23].
  - intros [H1|[H2|[H3|H4]]].
    + simpl. right. left. apply H1.
    + simpl. left. apply H2.
    + simpl. right. right. left. apply H3.
    + destruct H4.
  - intros [H1|[H2|[H3|H4]]].
    + simpl. left. apply H1.
    + simpl. right. right. left. apply H2.
    + simpl. right. left. apply H3.
    + destruct H4.
  - intros H. apply IH23. apply IH12. apply H.
Qed.

(* Exercise: 1 star, standard, optional (Perm3_NotIn) *)
Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2 E.
  induction E as [a b c|a b c|l1 l2 l3 E12 IH12 E23 IH23].
  - simpl. apply contrapositive. intros [H1|[H2|[H3|H4]]].
    + right. left. apply H1.
    + left. apply H2.
    + right. right. left. apply H3.
    + destruct H4.
  - simpl. apply contrapositive. intros [H1|[H2|[H3|H4]]].
    + left. apply H1.
    + right. right. left. apply H2.
    + right. left. apply H3.
    + destruct H4.
  - simpl. intros H. apply IH23. apply IH12. apply H.
Qed.

(* Exercise: 2 stars, standard, optional (NotPerm3) *)
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  simpl. intros H.
  apply Perm3_In with (x:=3) in H.
  - simpl in H. destruct H as [H1|[H2|[H3|H4]]].
    + discriminate H1.
    + discriminate H2.
    + discriminate H3.
    + destruct H4.
  - unfold In. right. right. left. reflexivity.
Qed.

(* Exercising with Inductive Relations *)
Module Playground.
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.
Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.
Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.

Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).
End Playground.

(* Exercise: 3 stars, standard, especially useful (le_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno.
  - apply Hmn.
  - apply le_S. apply IHHno. apply Hmn.
Qed.
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm.
  - apply le_n.
  - apply le_S in IHHnm. apply IHHnm.
Qed.
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H as [| n' m'].
  - apply le_n.
  - assert (H' : n <= S n).
    { apply le_S. apply le_n. }
    apply le_trans with (n:= S n).
    apply H'. apply H0.
Qed.
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - rewrite <- plus_n_O. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IHb.
Qed.

(* Exercise: 2 stars, standard, especially useful (plus_le_facts1) *)
Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  split.
  - assert (H1' : n1 <= n1 + n2).
    { apply le_plus_l. }
    apply le_trans with (n:= n1 + n2).
    apply le_plus_l. apply H.
  - assert (H2' : n2 <= n1 + n2).
    { rewrite add_comm. apply le_plus_l. }
    apply le_trans with (n:= n1 + n2).
    apply H2'. apply H.
Qed.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n.
  - intros H. left. apply O_le_n.
  - intros. destruct p.
    + rewrite plus_O_n in H.
      apply plus_le in H.
      destruct H.
      right. apply H0.
    + simpl in H.
      rewrite plus_n_Sm with n m in H.
      rewrite plus_n_Sm with p q in H.
      apply IHn in H. destruct H.
      * left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.
(**
  Note: Sometimes we should do fewer intros before induction to obtain a more general induction hypothesis.
*)
