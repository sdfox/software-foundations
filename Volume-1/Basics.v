From Coq Require Export String.

(* Bool *)
Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(* Numbers *)
Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

 Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(**Exercises**************************************************)
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
Definition ltb (n m : nat) : bool :=
  match m with
  | 0 => false
  | S m' => leb n m'
  end.

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
Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* andb_true_elim2 *)
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

(* identify_fn_applied_twice *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H2.
  intros b.
  rewrite H2.
  rewrite H2.
  reflexivity.
Qed.

(* negation_fn_applied_twice *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H2.
  destruct b eqn:E.
  - rewrite H2.
    rewrite H2.
    simpl.
    reflexivity.
  - rewrite H2.
    rewrite H2.
    simpl.
    reflexivity.
Qed.
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

(* andb_eq_orb *)
(* Note: ∀ b c : bool, b && c = b || c -> b = c *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + (* b:true c:true *)
      simpl.
      reflexivity.
    + (*b:true c:false *)
      simpl.
      intros H.
      rewrite H.
      reflexivity.
  - destruct c eqn:Ec.
    + (* b:false c:true *)
      simpl.
      intros H.
      rewrite H.
      reflexivity.
    + (* b:false c:false *)
      simpl.
      reflexivity.
Qed.

(* binary *)
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).
Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => mult 2 (bin_to_nat m')
  | B m' => mult 2 (bin_to_nat m') + 1
  end.
Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.

