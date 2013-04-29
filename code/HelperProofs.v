Require Export SfLib.
Require Export HelperFunctions.

(* 
 * Proofs about blt_nat
 *)
Theorem Sn_lt_Sm__n_lt_m : forall n m,
  S n < S m -> n < m.
Proof.
  induction n. intros m H. omega.
  intros m H. destruct m. inversion H. inversion H1. omega.
Qed.

Theorem blt_nat_n_m__blt_nat_Sn_Sm : forall n m,
  blt_nat n m = true -> blt_nat (S n)  (S m) = true.
Proof.
  intros n m H.  destruct m. inversion H.
  unfold blt_nat. unfold blt_nat in H. rewrite <- H. reflexivity.
Qed.

Theorem blt_nat_n_m_false__blt_nat_Sn_Sm : forall n m,
  blt_nat n m = false -> blt_nat (S n)  (S m) = false.
Proof.
  intros n m H.  destruct m. unfold blt_nat. simpl. reflexivity.
  unfold blt_nat. simpl. unfold blt_nat in H. simpl in H. apply H.
Qed.

Theorem n_lt_m__Sn_lt_Sm : forall n m,
  n < m -> S n < S m.
Proof.
  intros. induction H; omega.
Qed.
 
Theorem blt_nat_true : forall n m,
  blt_nat n m = true <-> n < m.
Proof. 
  split; generalize dependent m.
  Case "->".
    induction n.  intros m H.
    destruct m. inversion H. omega.
    intros m H. destruct m. inversion H. apply n_lt_m__Sn_lt_Sm. apply IHn. rewrite <- H.
    reflexivity.
  Case "<-".
    induction n. intros m H. destruct m. inversion H. unfold blt_nat. simpl. reflexivity.
    intros m H. destruct m. inversion H. apply Sn_lt_Sm__n_lt_m in H. apply blt_nat_n_m__blt_nat_Sn_Sm.  apply IHn.  apply H.
Qed.

Theorem blt_nat_false : forall n m,
  blt_nat n m = false <-> ~(n < m).
Proof. 
  split; generalize dependent m.
  Case "->".
    unfold not. intros. unfold blt_nat in H. apply ble_nat_false in H. omega.
  Case "<-".
    induction n. 
    SCase "n = 0". 
      intros. destruct m. unfold blt_nat. simpl. reflexivity.
      unfold not in H. apply ex_falso_quodlibet. apply H. omega.
    SCase "n = S n".
      intros. destruct m. compute. reflexivity.
      apply blt_nat_n_m_false__blt_nat_Sn_Sm.
      apply IHn.
      unfold not. unfold not in H.
      intro. apply H. 
      apply n_lt_m__Sn_lt_Sm. apply H0.
Qed.

Lemma n_lt_n_inversion : forall (n: nat) (P: Prop),
  n < n -> P.
Proof.
  intros. apply lt_not_le in H. unfold not in H. 
  apply ex_falso_quodlibet. apply H.
  omega.
Qed.

Lemma Sn_le_n_inversion : forall (n: nat) (P: Prop),
  S n <= n -> P.
Proof.
  intros. apply le_not_gt in H. unfold not in H.
  apply ex_falso_quodlibet. apply H.
  omega.
Qed.


Lemma ble_nat_symm : forall (n: nat),
  ble_nat n n = true.
Proof.
  intros. induction n.
  simpl. reflexivity.
  simpl. apply IHn.
Qed.

Lemma blt_nat_symm : forall (n: nat),
  blt_nat n n = false.
Proof.
  intros. induction n.
  unfold blt_nat. simpl. reflexivity.
  apply blt_nat_n_m_false__blt_nat_Sn_Sm. apply IHn.
Qed.

(*
 * Proofs about min_nat
 *)
Theorem min_nat_works : forall (n1 n2: nat),
  (n2 < n1 -> min_nat n2 n1 = n2) /\ (n1 > n2 -> min_nat n2 n1 = n2).
Proof.
  intros n1 n2;
  split; intros;
    unfold min_nat; remember (ble_nat n2 n1) as ble; destruct ble;
    try reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
 Qed.
  
Theorem min_nat_elim_n1 : forall (n1 n2: nat),
  n1 <= n2 <-> min_nat n1 n2 = n1.
Proof.
  split.
  Case "->".
    intros. unfold min_nat. remember (ble_nat n1 n2) as ble. destruct ble.
    reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold min_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.

Theorem min_nat_elim_n2 : forall (n1 n2: nat),
  n1 >= n2 <-> min_nat n1 n2 = n2.
Proof.
  split.
  Case "->".
    intros. unfold min_nat. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold min_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.



(*
 * Proofs about max_nat
 *)
Theorem max_nat_works : forall (n1 n2: nat),
  (n1 < n2 -> max_nat n1 n2 = n2) /\ (n2 < n1 -> max_nat n1 n2 = n1). 
Proof.
  intros n1 n2.
  split; intros; 
    unfold max_nat; remember (ble_nat n1 n2) as ble; destruct ble; 
    try reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
Qed.

Theorem max_nat_elim_n1 : forall (n1 n2: nat),
  n1 <= n2 <-> max_nat n1 n2 = n2.
Proof.
  split.
  Case "->".
    intros. unfold max_nat. remember (ble_nat n1 n2) as ble. destruct ble.
    reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold max_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.
    
Theorem max_nat_elim_n2 : forall (n1 n2: nat),
  n1 >= n2 <-> max_nat n1 n2 = n1.
Proof.
  split.
  Case "->".
    intros. unfold max_nat. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold max_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.



(*
 * Lenght lemmas
 *)
Lemma length_0_impl_nil : forall (X: Type) (l: list X),
  length l = 0 -> l = [].
Proof.
  intros. induction l.
  reflexivity.
  simpl in H. inversion H.
Qed.
Lemma length_gt_0_impl_nil : forall (X: Type) (l: list X),
  length l <= 0 -> l = [].
Proof.
  intros. induction l.
  reflexivity.
  simpl in H. inversion H.
Qed.


Lemma app_length_le_l1 : forall (X: Type) (l l1 l2: list X),
  l1 ++ l2 = l -> length l1 <= length l.
Proof.
  intros. generalize dependent l1.
  induction l.
  Case "l = []".
    intros. apply app_eq_nil in H. inversion H. subst. simpl. omega.
  Case "l = a::l".
    intros. destruct l1. simpl. omega.
    rewrite <- app_comm_cons in H.
    inversion H. rewrite H2.
    simpl. apply le_n_S. apply IHl. apply H2.
Qed.

Lemma rev_app_cons : forall (X: Type) (x: X) (l1 l2: list X),
  rev l1 ++ x :: l2 = rev (x::l1) ++ l2.
Proof.
  intros. simpl. rewrite <- app_assoc. simpl. reflexivity.
Qed.
