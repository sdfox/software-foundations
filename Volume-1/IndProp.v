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

(* Exercise: 2 stars, standard, especially useful (plus_le_facts2) *)
Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p H.
  induction p.
  - simpl. apply H.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHp.
Qed.
Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  rewrite add_comm.
  assert (H' : m + p = p + m).
  { rewrite add_comm. reflexivity. }
  rewrite H'.
  apply plus_le_compat_l.
  apply H.
Qed.
Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  induction p.
  - rewrite add_0_r. apply H.
  - simpl. apply le_S in IHp.
    rewrite <- plus_n_Sm.
    apply IHp.
Qed.

(* Exercise: 3 stars, standard, optional (lt_facts) *)
Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m. generalize dependent n.
  induction m.
  - right. unfold ge. apply O_le_n.
  - induction n.
    + left. unfold lt. rewrite <- PeanoNat.Nat.add_1_r.
      assert (H' : S m = m + 1).
      { rewrite <- PeanoNat.Nat.add_1_r. reflexivity. }
      rewrite H'. apply plus_le_compat_r. apply O_le_n.
    + destruct IHn. inversion H.
      * right. unfold ge. apply le_n.
      * left. unfold lt.
        apply n_le_m__Sn_le_Sm. apply H2.
      * right. unfold ge. unfold ge in H. apply le_S in H. apply H.
Qed.
Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  destruct n.
  - intros m H. apply O_le_n.
  - intros m H. unfold lt in H. apply le_S in H.
    apply Sn_le_Sm__n_le_m in H. apply H.
Qed.
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  split.
  - unfold lt. unfold lt in H. rewrite <- plus_Sn_m in H.
    apply le_trans with (n:=S n1 + n2).
    apply le_plus_l. apply H.
  - unfold lt. unfold lt in H. rewrite <- plus_Sn_m in H.
    apply le_trans with (n:= S n1 + n2).
    rewrite PeanoNat.Nat.add_succ_comm. rewrite add_comm.
    apply le_plus_l. apply H.
Qed.

(* Exercise: 4 stars, standard, optional (leb_le) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n.
  - intros m H. apply O_le_n.
  - induction m.
    + simpl. intros H. discriminate H.
    + simpl. intros H. apply n_le_m__Sn_le_Sm.
      apply IHn in H. apply H.
Qed.
Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  induction n.
  - intros m H. simpl. reflexivity.
  - induction m.
    + intros H. inversion H.
    + intros H. simpl.
      apply Sn_le_Sm__n_le_m in H. apply IHn in H.
      apply H.
Qed.
(* Hint: The next two can easily be proved without using induction. *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_iff. apply le_trans with (n:=m).
  apply leb_iff in Hnm. apply Hnm.
  apply leb_iff in Hmo. apply Hmo.
Qed.

Module R.
(* Exercise: 3 stars, standard, especially useful (R_provability) *)
Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R n m o
.

Example R112 : R 1 1 2.
Proof.
  apply c3.
  apply c2.
  apply c1.
Qed.
Example R226 : R 2 2 6.
Proof.
Abort.
(**
1.
R 1 1 2 provable
R 2 2 6 unprovable
2.
Drop constructor c5, the set of provable propositions would not change.
Because any proposition apply c5 can only get the proposition same as itself.
3.
If we dropped constructor c4 from the definition of R, the set of provable propositions would change.
Because applying c4 can change a proposition in a specific way.
*)
Definition manual_grade_for_R_provability : option (nat*string) := None.

(* Exercise: 3 stars, standard, optional (R_fact) *)
Definition fR : nat -> nat -> nat :=
  plus.
Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o.
  split.
  - simpl. unfold fR. intros H. induction H.
    + simpl. reflexivity.
    + simpl. apply eq_S. apply IHR.
    + rewrite <- plus_n_Sm. apply eq_S. apply IHR.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR. apply eq_add_S in IHR. apply eq_add_S in IHR. apply IHR.
    + rewrite add_comm. apply IHR.
  - generalize dependent n. generalize dependent m. generalize dependent o.
    unfold fR.
    assert (H1 : forall n1, R n1 0 n1).
    { induction n1. - apply c1. - apply c2. apply IHn1. }
    assert (H2 : forall n2, R 0 n2 n2).
    { induction n2. - apply c1. - apply c3. apply IHn2. }
    induction m.
    + simpl. intros n H. rewrite H. apply H2.
    + simpl. intros n H. apply c4. apply c2. apply c2.
      Search (S (_ + _) = _ + S _). rewrite plus_n_Sm in H.
      apply IHm in H. apply H.
Qed.
End R.

(* Exercise: 4 stars, advanced (subsequence) *)
Inductive subseq : list nat -> list nat -> Prop :=
  | s1 (l : list nat) : subseq [] l
  | s2 (l1 l2 : list nat) (h : nat) (H : subseq l1 l2) : subseq (h :: l1) (h :: l2)
  | s3 (l1 l2 : list nat) (h : nat) (H : subseq l1 l2) : subseq l1 (h :: l2)
.
(**
  same as:
Inductive subseq : list nat -> list nat -> Prop :=
  | s1 : forall (l : list nat) ,subseq [] l
  | s2 : forall (l1 l2 : list nat) (h : nat), subseq l1 l2 -> subseq (h :: l1) (h :: l2)
  | s3 : forall (l1 l2 : list nat) (h : nat), subseq l1 l2 -> subseq l1 (h :: l2)
.
*)
Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l.
  induction l.
  - apply s1.
  - simpl. apply s2. apply IHl.
Qed.
Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  induction H.
  - simpl. apply s1.
  - simpl. apply s2. apply IHsubseq.
  - simpl. apply s3. apply IHsubseq.
Qed.
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
(* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
Proof.
  intros l1 l2 l3 H12 H23.
  generalize dependent H12.
  generalize dependent l1.
  induction H23.
  - intros l1 H. inversion H. apply s1.
  - intros. inversion H12.
    + apply s1.
    + apply s2. apply IHsubseq. apply H1.
    + apply s3. apply IHsubseq. apply H1.
  - intros. apply s3. apply IHsubseq. apply H12.
Qed.

(* Exercise: 2 stars, standard, optional (R_provability2) *)
Inductive R : nat -> list nat -> Prop :=
  | c1                    : R 0     []
  | c2 n l (H: R n     l) : R (S n) (n :: l)
  | c3 n l (H: R (S n) l) : R n     l.
(**
  R 2 [1;0]       provable
  R 1 [1;2;1;0]   unprovable
  R 6 [3;2;1;0]   unprovable.
*)
(* Exercise: 2 stars, standard, optional (total_relation) *)
Inductive total_relation : nat -> nat -> Prop :=
  | t1 : total_relation 0 0
  | t2 : forall (m n : nat), total_relation (S m) n
  | t3 : forall (m n : nat), total_relation m (S n)
.
Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros n m.
  induction n.
  - induction m.
    + apply t1.
    + apply t3.
  - apply t2.
Qed.
(* Exercise: 2 stars, standard, optional (empty_relation) *)
Inductive empty_relation : nat -> nat -> Prop :=
.
Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(* Case Study: Regular Expressions *)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.
Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.
Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.
Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.
Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(* Exercise: 3 stars, standard (exp_match_ex1) *)
Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.
Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H|H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl. apply MStar0.
  - simpl. apply (MStarApp x).
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s H'.
      apply H. simpl. right. apply H'.
Qed.

(* Exercise: 2 stars, standard, optional (EmptyStr_not_needed) *)
Definition EmptyStr' {T:Type} := @Star T (EmptySet).
Lemma EmptyStr2EmptyStr' : forall T (s: list T),
  s =~ EmptyStr <-> s =~ EmptyStr'.
Proof.
  intros T s.
  split.
  - intros H.
    inversion H.
    unfold EmptyStr'.
    apply MStar0.
  - intros H.
    inversion H.
    + apply MEmpty.
    + inversion H2.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.
Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(* Exercise: 4 stars, standard (re_not_empty) *)
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App r1 r2 => andb (re_not_empty r1) (re_not_empty r2)
  | Union r1 r2 => orb (re_not_empty r1) (re_not_empty r2)
  | Star re => true
  end.
Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* FILL IN HERE *) Admitted.