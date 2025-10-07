From LF Require Export Poly.

(* The Apply Tactic *)
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2.
  apply eq1.
  apply eq3.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H. Qed.

(* Exercise: 2 stars, standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  Search rev.
  symmetry.
  apply rev_involutive.
Qed.

(* The apply with Tactic *)
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. Qed.

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (y:=[c;d]).
  apply eq1. apply eq2. Qed.

(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2. apply eq1.
Qed.

(* The injection and discriminate Tactics *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hmn.
  apply Hmn.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
   (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* Exercise: 3 stars, standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  injection eq1 as H1 H2.
  rewrite H1.
  symmetry.
  assert (H3: y :: l = z :: l -> y = z).
  { intros H'. injection H' as H''. apply H''. }
  apply H3.
  rewrite H2.
  rewrite <- eq2.
  reflexivity.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

(* Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - simpl.
    intros H.
    discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

(* Using Tactics on Hypotheses *)
Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

(* Specializing Hypotheses *)
Theorem specialize_example: forall n,
     (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.

(* Varying the Induction Hypothesis *)
Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
Abort.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = Sm' *)
      f_equal.
      apply IHn'.
      simpl in eq.
      injection eq as goal.
      apply goal.
Qed.

(* Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - destruct m as [| m'].
    + reflexivity.
    + intros H. discriminate H.
  - destruct m as [| m'].
    + intros H. discriminate.
    + intros H. f_equal.
      apply IHn'.
      simpl in H.
      apply H.
Qed.

(* Exercise: 2 stars, advanced (eqb_true_informal) *)
(**
  Theorem: for any n m, if n =? m = true, then n = m.
  Proof: let n be a nat. We proof by induction on n that, for any n, if n =? m = true, then n = m.
    First, suppose n = 0. And suppose m is a number such that 0 =? m = true, we must show that 0 = m.
    There are two cases to consider for m.
    If m = 0, by the definition of =?, we have true = true -> 0 = 0, we are done.
    If m = S m', so we have the form of (0 =? S m'), we derive a contradiction, we directly proved by the principle of explosion.

    Second, suppose n = S n', we must show that for all m, (S n' =? m) = true -> S n' = m, with the
    induction hypothesis that for all m, (n' =? m) = true -> n' = m.
    There are also two cases for m.
    If m = 0, the subgoal we must prove is (S n' =? 0) = true -> S n' = 0, also can be directly proved by contradiction.
    If m = S m', we must show (S n' =? S m') = true -> S n' = S m'.
    Intros the hyphothesis first. Then with the lemma f_equal, we can simplify the goal to n' = m'.
    Apply the induction hyphothesis to prove backward, to prove n' = m', we must prove (n' =? m') = true, while it is same with the hyphothesis we introduced.
    Qed.
*)
(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.

(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    destruct m as [| m'].
    + simpl. intros eq. apply eq.
    + simpl. intros eq. discriminate.
  - simpl.
    destruct m as [| m'].
    + simpl. intros eq. discriminate.
    + simpl. intros eq. f_equal.
      apply IHn'.
      rewrite <- plus_n_Sm in eq.
      rewrite <- plus_n_Sm in eq.
      injection eq as H.
      apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* We are stuck here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(* Rewriting with conditional statements *)
Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m H. rewrite add_0_r. destruct m as [| m'].
    + (* m = 0 *)
      reflexivity.
    + (* m = S m' *)
      reflexivity.
  - (* n = S n' *)
    intros m H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      simpl in H. simpl. rewrite <- plus_n_Sm.
      rewrite IHn'.
      * reflexivity.
      * apply H.
Qed.

(* Exercise: 3 stars, standard, especially useful (gen_dep_practice) *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t IHl].
  - simpl.
    intros H.
    reflexivity.
  - simpl.
    destruct n as [].
    + simpl.
      discriminate.
    + simpl.
      intros H.
      injection H as goal.
      apply IHl.
      apply goal.
Qed.

(* Unfolding Definitions *)
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.
Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* Using destruct on Compound Expressions *)
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.

(* Exercise: 3 stars, standard (combine_split) *)
Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IHl].
  - simpl.
    intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    reflexivity.
  - destruct h as [x y].
    simpl.
    destruct (split t).
    intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    f_equal.
    apply IHl.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.
Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - (* e3 = true *) apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
    destruct (n =? 5) eqn:Heqe5.
    + (* e5 = true *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + (* e5 = false *) discriminate eq. Qed.

(* Exercise: 2 stars, standard (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - (* b = true, f (f (f true)) = f true *)
    destruct (f true) eqn:E1.
    + (* f true = true *)
      rewrite E1.
      rewrite E1.
      reflexivity.
    + (* f true = false *)
      destruct (f false) eqn:E2.
      * (* f false = true *) apply E1.
      * (* f false = false *) apply E2.
  - (* b = false *)
    destruct (f false) eqn:E1.
    + (* f false = true *)
      destruct (f true) eqn:E2.
      * (* f true = true *) apply E2.
      * (* f true = false *) apply E1.
    + (* f false = false *)
      rewrite E1.
      rewrite E1.
      reflexivity.
Qed.

(* Additional Exercises *)
(* Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [].
  - simpl.
    destruct m.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - simpl.
    destruct m.
    + simpl.
      reflexivity.
    + rewrite IHn.
      simpl.
      reflexivity.
Qed.

(* Exercise: 3 stars, advanced, optional (eqb_sym_informal) *)
(**
  Theorem: for any n: nat, m: nat, (n =? m) = (m =? n).
  Proof: induction on n.
  First, n = 0, we must show that forall m, (0 =? m) = (m =? 0).
  We can destruct m as zero or non-zero. If m = 0, (0 =? 0) = (0 =? 0) holds.
  If m != 0, we can deduce from (0 =? m) = (m =? 0) to false = false, the equation holds.

  Second, n' = S n, we must show that forall m, (n' =? m) = (m =? n'), since we have the induction hypothesis forall m, (n =? m) = (m =? n).
  Classify m as zero or non-zero.
  If m = 0, we must show that (S n =? 0) = (0 =? Sn). Since (S n =? 0) = false, (0 =? Sn) = false too, the equation holds.
  If m != 0, we must show that (n =? m) = (S m =? S n), from induction hypothesis we can get (m =? n) = (S m =? S n). After simplify the equation holds.
*)

(* Exercise: 3 stars, standard, optional (eqb_trans) *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eq1 eq2.
  Search eqb.
  apply eqb_true in eq1.
  apply eqb_true in eq2.
  rewrite <- eq2.
  rewrite -> eq1.
  apply eqb_refl.
Qed.

(* Exercise: 3 stars, advanced (split_combine) *)
Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
:=  forall X Y (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1 as [| h1 t1 IHl].
  - intros l2.
    destruct l2.
    + simpl.
      reflexivity.
    + discriminate.
  - intros l2 H.
    destruct l2 as [| h2 t2].
    + discriminate.
    + injection H as H.
      simpl.
      rewrite IHl.
      * simpl.
        reflexivity.
      * apply H.
Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.

(* Exercise: 3 stars, advanced (filter_exercise) *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l lf.
  induction l as [| h t IHl].
  - simpl. discriminate.
  - simpl. destruct (test h) eqn:E.
    + intros H. injection H as H. rewrite <- H. apply E.
    + apply IHl.
Qed.

(* Exercise: 4 stars, advanced, especially useful (forall_exists_challenge) *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t
              else false
  end.
Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => if test h then true
              else existsb test t
  end.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.
Check negb.
Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun (x : X) => (negb (test x))) l).
Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| h t IHl].
  - unfold existsb'.
    simpl.
    reflexivity.
  - simpl.
    destruct (test h) eqn:E.
    + unfold existsb'.
      simpl.
      rewrite E.
      reflexivity.
    + simpl.
      rewrite IHl.
      unfold existsb'.
      simpl.
      rewrite E.
      simpl.
      reflexivity.
Qed.