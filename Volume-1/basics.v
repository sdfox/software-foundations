(* nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  if b1 then
    if b2 then false
    else true
  else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* andb3 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => match b3 with
                      | true => true
                      | false => false
                      end
            | false => false
            end
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* factorial *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (mult (S n') (factorial n'))
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* ltb *)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  match m with
  | 0 => false
  | S m' => leb n m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* plus_id_exercise *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H0.
  rewrite H0.
  intros H1.
  rewrite <- H1.
  reflexivity.
Qed.

(* mult_n_1 *)
Notation "x * y" := (mult x y).
Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* andb_true_elim2 *)
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  - simpl.
    destruct c eqn:Ec.
    + intros H.
      reflexivity.
    + intros H.
      rewrite -> H.
      reflexivity.
Qed.

(* zero_nbeq_plus_1 *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - simpl.
    reflexivity.
  -simpl.
   reflexivity.
Qed.
