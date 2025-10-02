From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

(**Exercise************************************************)
(* basic_induction *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite add_0_r.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(* double_plus *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

(* eqb_refl *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(* even_S *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - rewrite IHn'.
    simpl.
    destruct (even n').
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

(** add_comm_informal
  Theorem: For any n, m, n + m = m + n
  Proof: By induction on n.
    First, suppose n = 0. We must show that
      0 + m = m + 0.
    By the definition of + and Theorem add_0_r, we can simplify it to
      m = m.
    Subproof complete.

    Second, the induction hypothesis is n' + m = m + n'
    Suppose n = S n', we must show that
      S n' + m' = m + Sn'
    We can simplify it to
      S (n'+ m) = m + S n'
    Rewrite the right part with Theorem plus_n_Sm: for all n m, nat, S (n + m) = n + (S m).
      S (n' + m) = S (m + n')
    Rewrite again with the induction hypothesis.
      S (n' + m) = S (n' + m)
  Qed.
*)

(** eqb_refl_informal
  Theorem:  forall n : nat, (n =? n) = true.
  Proof: By induction on n.
    First, suppose n = 0. We must show that
      0 =? 0 = true.
    Obviously proof by the definition of =?.
    Second, induction hypothesis: n' =? n' = true.
    Suppose n = S n', we must show that
      S n' =? S n' = true.
    We can simplify the left part to n' =? n' by using theorem plus_n_Sm
    Immediate from the induction hypothesis.
  Qed.
*)

(* mul_comm *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem mul_m_Sn : forall n m : nat,
  m * (S n) = m * n + m.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHm'.
    rewrite <- plus_n_Sm.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite mul_0_r.
    reflexivity.
  - simpl.
    rewrite mul_m_Sn.
    rewrite IHn'.
    rewrite add_comm.
    reflexivity.
Qed.

(* add_shuffle3' *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm.
    reflexivity.
Qed.

(* nat to bin and back to nat *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => mult 2 (bin_to_nat m')
  | B1 m' => mult 2 (bin_to_nat m') + 1
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  simpl.
  assert (H: forall m : nat, S m  = m + 1).
    { intros m.
      induction m as [].
      + simpl.
        reflexivity.
      + simpl.
        rewrite IHm.
        reflexivity.
     }
  induction b as [].
  - simpl.
    reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite plus_n_Sm.
    replace (S (bin_to_nat b)) with (bin_to_nat b + 1).
    + rewrite add_assoc.
      reflexivity.
    + rewrite <- H.
      reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite add_0_r.
    rewrite H.
    rewrite IHb.
    rewrite H.
    rewrite add_assoc.
    set (B:= bin_to_nat b) in *.
    replace (B + 1 + B) with (B + B + 1).
    + simpl.
      reflexivity.
    + simpl.
      assert (H0: B + B + 1 = B + (B + 1)).
      {simpl. rewrite add_assoc. reflexivity. }
      rewrite H0.
      rewrite add_comm.
      reflexivity.
Qed.
