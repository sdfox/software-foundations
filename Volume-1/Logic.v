From LF Require Export Tactics.

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

(* Logical Connectives *)
(* Conjunction *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Check @conj : forall A B : Prop, A -> B -> A /\ B.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(* Exercise: 2 stars, standard (plus_is_O) *)
Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  destruct n eqn:E.
  - simpl.
    intros H.
    split.
    + reflexivity.
    + apply H.
  - simpl.
    discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.

(* Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [_ HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

(* Exercise: 1 star, standard (and_assoc) *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and : Prop -> Prop -> Prop.

(* Disjunction *)
Check or : Prop -> Prop -> Prop.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Exercise: 2 stars, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n eqn:En.
  - left. reflexivity.
  - right. destruct m eqn:Em.
    + reflexivity.
    + discriminate H.
Qed.

(* Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP|HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* Falsehood and Negation *)
Definition not (P:Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

(* Exercise: 2 stars, standard, optional (not_implies_our_not) *)
Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.
  intros P H1 Q H2.
  apply H1 in H2.
  destruct H2.
Qed.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(* Exercise: 2 stars, advanced (double_neg_informal) *)
(**
  Theorem: P implies ~~P, for any proposition P.
  Proof: First, we have P.
         Suppose ~P is true, we have a contradictory.
         So ~P is not true, we have ~~P.
         P -> ~~P holds.
*)
(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_informal : option (nat*string) := None.

(* Exercise: 1 star, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros contra.
  intros HP.
  apply H in HP.
  apply contra in HP.
  apply HP.
Qed.

(* Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [HP contra].
  apply contra in HP.
  destruct HP.
Qed.

(* Exercise: 1 star, advanced (not_PNP_informal) *)
(**
  Theorem: forall P : Prop, ~(P /\ ~P).
  Proof: First, we have P.
         Suppose ~P, we have P /\ ~P, but proposition P and proposition ~P make a contra.
         So (P /\ ~P) is not true, we have ~(P /\ ~P).
*)
(* Do not modify the following line: *)
Definition manual_grade_for_not_PNP_informal : option (nat*string) := None.

(* Exercise: 2 stars, standard (de_morgan_not_or) *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q H.
  split.
  - intros HP.
    assert (H2: P -> P \/ Q).
    { intros eq. left. apply eq. }
    apply H2 in HP.
    apply H in HP.
    destruct HP.
  - intros HQ.
    assert (H3: Q -> P \/ Q).
    { intros eq. right. apply eq. }
    apply H3 in HQ.
    apply H in HQ.
    destruct HQ.
Qed.

(* Exercise: 1 star, standard, optional (not_S_inverse_pred) *)
Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  intros H.
  specialize H with (n:=O).
  simpl in H.
  discriminate H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* Truth *)
Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(* Exercise: 2 stars, advanced, optional (nil_is_not_cons) *)
Definition empty (X:Type) (l : list X) :=
  match l with
  | [] => True
  | h :: t => False
  end.
Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  intros X x.
  destruct xs as [|h t].
  - simpl.
    unfold not.
    intros contra.
    assert (H : empty X []). { simpl. apply I. }
    rewrite contra in H. simpl in H. apply H.
  - simpl.
    unfold not.
    intros contra.
    assert (H : empty X []). { simpl. apply I. }
    rewrite contra in H. simpl in H. apply H.
Qed.

(* Logical Equivalence *)
Print "<->".

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.
Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

(* Exercise: 1 star, standard, optional (iff_properties) *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros H. apply H.
  - intros H. apply H.
Qed.
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HAB HBA] [HBC HCB].
  split.
  - intros H. apply HAB in H. apply HBC in H. apply H.
  - intros H. apply HCB in H. apply HBA in H. apply H.
Qed.

(* Exercise: 3 stars, standard (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - (* P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R). *)
    intros [HP|HQR].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * destruct HQR as [HQ _]. right. apply HQ.
      * destruct HQR as [_ HR]. right. apply HR.
  - (* (P \/ Q) /\ (P \/ R). -> P \/ (Q /\ R) *)
    intros [[HP1|HQ] [HP2|HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

(* Setoids and Logical Equivalence *)
From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* Existential Quantification *)
Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.
Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note the implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

(* Exercise: 1 star, standard, especially useful (dist_not_exists) *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros X P H1 H2.
  destruct H2 as [x Hx].
  apply Hx in H1.
  destruct H1.
Qed.

(* Exercise: 2 stars, standard (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [t [Ht1|Ht2]].
    + left. exists t. apply Ht1.
    + right. exists t. apply Ht2.
  - intros [[t Ht]|[t Ht]].
    + exists t. left. apply Ht.
    + exists t. right. apply Ht.
Qed.

(* Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  induction n as [| n' IHn].
  - simpl. intros m H. exists m. reflexivity.
  - destruct m as [|m'].
    + simpl. discriminate.
    + simpl. intros H.
      apply IHn in H.
      destruct H as [t Ht].
      exists t. rewrite Ht.
      reflexivity.
Qed.
Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  induction n.
  - simpl. reflexivity.
  - intros m H.
    simpl in H.
    destruct m as [|m'].
    + destruct H as [x H]. discriminate H.
    + destruct H as [x H]. injection H as H.
      simpl. apply IHn. exists x. apply H.
Qed.

(* Programming with Propositions *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* Exercise: 2 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + simpl. intros contra. destruct contra.
    + simpl. intros [H|H].
      * exists x. split.
        { apply H. }
        { left. reflexivity. }
      * apply IHl' in H. destruct H as [x' [H1 H2]].
        exists x'. split.
        { apply H1. }
        { right. apply H2. }
  - induction l as [|x l' IHl'].
    + simpl. intros H. destruct H as [x [_ contra]]. apply contra.
    + simpl. intros [x' [H1[H2|H3]]].
      * left. rewrite <- H2 in H1. apply H1.
      * right. apply IHl'.
        exists x'. split.
        { apply H1. }
        { apply H3. }
Qed.

(* Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - simpl. split.
    + intros H. right. apply H.
    + intros [H|H].
      { destruct H. }
      { apply H. }
  - simpl. split.
    + intros [H|H].
      { left. left. apply H. }
      { apply IH in H. destruct H as [H|H].
        { left. right. apply H. }
        { right. apply H. }
      }
    + intros [[H|H]|H].
      { left. apply H. }
      { right. apply IH. left. apply H. }
      { right. apply IH. right. apply H. }
Qed.

(* Exercise: 3 stars, standard, especially useful (All) *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.
Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P. split.
  - induction l as [| h t IHl].
    + simpl. intros H. apply I.
    + simpl. intros H. split.
      { apply H. left. reflexivity. }
      { apply IHl. intros x H2. apply H. right. apply H2. }
  - induction l as [| h t IHl].
    + simpl. intros Ht x Hf. destruct Hf.
    + simpl. intros [H1 H2] x [H|H].
      { rewrite <- H. apply H1. }
      { apply IHl in H.
        { apply H. }
        { apply H2. }
      }
Qed.

(* Exercise: 2 stars, standard, optional (combine_odd_even) *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n : nat) => if (odd n) then Podd n
                   else Peven n.
Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  destruct (odd n) eqn:E.
  - unfold combine_odd_even.
    rewrite E. apply H1. reflexivity.
  - unfold combine_odd_even.
    rewrite E. apply H2. reflexivity.
Qed.
Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  destruct (odd n) eqn:E.
  - unfold combine_odd_even. rewrite E.
    intros H1 H2. apply H1.
  - unfold combine_odd_even. rewrite E.
    intros H1 H2. discriminate H2.
Qed.
Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  destruct (odd n) eqn:E.
  - unfold combine_odd_even. rewrite E.
    intros H1 H2. discriminate H2.
  - unfold combine_odd_even. rewrite E.
    intros H1 H2. apply H1.
Qed.

(* Applying Theorems to Arguments *)
Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

Check add_comm : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l-> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Working with Decidable Properties *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the even_S lemma from Induction.v. *)
  induction n as [| n' IHn'].
  - simpl. exists 0. simpl. reflexivity.
  - Check even_S. destruct (even (S n')) eqn:E.
    + rewrite even_S in E.
      assert (H: negb (even n') = true -> even n' = false).
      { destruct (even n').
        { simpl. discriminate. }
        { simpl. intros eq. reflexivity. } }
      apply H in E. rewrite E in IHn'. destruct IHn' as [k' Hk'].
      exists (S k'). rewrite Hk'. simpl. reflexivity.
    + rewrite even_S in E.
      assert (H: negb (even n') = false -> even n' = true).
      { destruct (even n').
        { simpl. intros eq. reflexivity. }
        { simpl. discriminate. } }
      apply H in E. rewrite E in IHn'. destruct IHn' as [k' Hk'].
      exists k'. rewrite Hk'. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Fail
Definition is_even_prime (n : nat) : bool :=
  if n = 2 then true
  else false.

Definition is_even_prime (n : nat) : bool :=
  if n =? 2 then true
  else false.

Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. reflexivity. Qed.
Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.
Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.
Example not_even_1001' : ~(Even 1001).
Proof.
  unfold not.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Exercise: 2 stars, standard (logical_connectives) *)
Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  - intros H. destruct b1 eqn:E.
    + split.
      { reflexivity. }
      { simpl in H. apply H. }
    + split.
      { discriminate. }
      { simpl in H. discriminate H. }
  - intros [H1 H2].
    rewrite H1. rewrite H2. simpl. reflexivity.
Qed.
Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  split.
  - intros H. destruct b1 eqn:E.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [H|H].
    + rewrite H. simpl. reflexivity.
    + rewrite H. simpl. destruct b1.
      { simpl. reflexivity. }
      { simpl. reflexivity. }
Qed.

(* Exercise: 1 star, standard (eqb_neq) *)
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H. destruct (x =? y) eqn:E.
    + discriminate H.
    + unfold not. intros eq.
      rewrite eq in E. rewrite eqb_refl in E. discriminate E.
  - unfold not. intros H1.
    apply not_true_iff_false.
    intros H2. apply eqb_eq in H2. apply H1 in H2. destruct H2.
Qed.

(* Exercise: 3 stars, standard (eqb_list) *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
                  :=
  match l1,l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1 :: t1, h2 :: t2 => match (eqb h1 h2) with
                          | true => eqb_list eqb t1 t2
                          | false => false
                          end
  end.
Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb. induction l1 as [| h1 t1 IHl1].
  - split.
    + simpl. destruct l2.
      { intros eq. reflexivity. }
      { discriminate. }
    + simpl. destruct l2.
      { intros eq. reflexivity. }
      { discriminate. }
  - split.
    + destruct l2 as [|h2 t2] eqn:E.
      { simpl. discriminate. }
      { simpl. destruct (eqb h1 h2) eqn:Eh.
        { simpl. apply H in Eh. rewrite Eh. intros H2. f_equal. apply IHl1 in H2. apply H2. }
        { discriminate. } }
    + destruct l2 as [|h2 t2] eqn:E.
      { simpl. discriminate. }
      { simpl. destruct (eqb h1 h2) eqn:Eh.
        { simpl. apply H in Eh. rewrite Eh. intros H2. injection H2 as H2. apply IHl1. apply H2. }
        { simpl in Eh. intros H2. injection H2 as H2. rewrite H2 in Eh. Search eqb. rewrite <- Eh. apply H. reflexivity. } }
Qed.

(* Exercise: 2 stars, standard, especially useful (All_forallb) *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t
              else false
  end.
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test.
  induction l as [| h t IHl].
  - split.
    + simpl. intros H. apply I.
    + simpl. intros H. reflexivity.
  - split.
    + simpl. destruct (test h) eqn:E.
      { intros H. split.
        { reflexivity. }
        { apply IHl in H. apply H. } }
      { discriminate. }
    + simpl. destruct (test h) eqn:E.
      { intros [_ H]. apply IHl. apply H. }
      { intros [contra _]. discriminate contra. }
Qed.

(* The Logic of Coq *)
(* Functional Extensionality *)
Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(* Exercise: 4 stars, standard (tr_rev_correct) *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality. intros l.
  induction l as [|h t IHl].
  - unfold tr_rev. simpl. reflexivity.
  - simpl. rewrite <- IHl. unfold tr_rev.
    assert (H1: forall (T : Type) (x : T) (l : list T), rev_append (x :: l) [] = rev_append l [x]).
    { simpl. reflexivity. }
    rewrite H1.
    assert (H2: forall (T : Type) (l1 l2 : list T), rev_append l1 l2 = rev_append l1 [] ++ l2).
    { intros T. induction l1 as [| h1 t1 IHl1].
      { simpl. reflexivity. }
      { simpl. intros l2. rewrite IHl1. rewrite (IHl1 [h1]). rewrite <- app_assoc. simpl. reflexivity. }
    }
    apply H2.
Qed.

(* Classical vs. Constructive Logic *)
Definition excluded_middle := forall P : Prop,
  P \/ ~ P.
Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. destruct H as [H1 H2]. unfold not. intros H. apply H1 in H. discriminate H.
Qed.

(* Exercise: 3 stars, standard (excluded_middle_irrefutable) *)
Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  intros H.
  apply H.
  right. intros HP.
  apply H. left. apply HP.
Qed.

(* Exercise: 3 stars, advanced (not_exists_dist) *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros LEM.
  intros X P H x.
  Print excluded_middle.
  destruct LEM with (P:= P x) as [HP|HNP].
  - apply HP.
  - unfold not in HNP.
    unfold not in H.
    assert (H': exists x : X, P x -> False).
    { exists x. apply HNP. }
    apply H in H'. destruct H'.
Qed.

(* Exercise: 5 stars, standard, optional (classical_axioms) *)
Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).
Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.
Theorem classical_axioms :excluded_middle -> peirce -> double_negation_elimination -> de_morgan_not_and_not -> implies_to_or -> consequentia_mirabilis -> excluded_middle.
Proof.
  intros LEM peirce double_negation_elimination de_morgan_not_and_not implies_to_or consequentia_mirabilis.
  apply LEM.
Qed.