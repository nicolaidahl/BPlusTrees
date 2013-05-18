Require Export SfLib.
Require Export HelperFunctions.
Require Export SplitCutList.
Require Export ValidBPlusTree.
Require Export InductiveDataTypes.


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

Lemma blt_nat_symm : forall (n: nat),
  blt_nat n n = false.
Proof.
  intros. induction n.
  unfold blt_nat. simpl. reflexivity.
  apply blt_nat_n_m_false__blt_nat_Sn_Sm. apply IHn.
Qed.

(*
 * Proofs about ble_nat and <= 
 *)

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

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m <-> S n <= S m.
Proof.
  split; intros; omega.
Qed.

(* 
 * Proofs about beq_nat and = 
 *)

Lemma eq_remove_S : forall (n m: nat),
  n = m -> S n = S m.
Proof.
  intros.
  omega.
Qed.


(*
 * Proofs about between (ble && ble)
 *)

Lemma ble_and_blt_true: forall n m k,
  ble_nat n k && blt_nat k m = true ->
  n <= k < m.
Proof.
  intros. unfold andb in H. remember (ble_nat n k). destruct b. apply blt_nat_true in H.
  symmetry in Heqb. apply ble_nat_true in Heqb. omega. inversion H.
Qed.

Lemma ble_and_blt_false: forall n m k,
  ble_nat n k && blt_nat k m = false ->
  n > k \/ k >= m.
Proof.
  intros. unfold andb in H. remember (ble_nat n k). destruct b. symmetry in Heqb.
  apply ble_nat_true in Heqb. apply blt_nat_false in H. right. omega. 
  symmetry in Heqb. apply ble_nat_false in Heqb. left. omega.
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
 * Other list-related proofs
 *)

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

Lemma app_list_eq_list_list : forall (X: Type) (l1 l2: list X),
  l1 ++ l2 = l1 -> l2 = [].
Proof.
  intros.
  induction l1. simpl in H. apply H.
  apply IHl1. simpl in H. SearchAbout [cons].
  inversion H. rewrite H1. apply H1.
Qed.

Lemma cons_remove : forall (X: Type) (x: X) (l1 l2: list X),
  x :: l1 = x :: l2 <-> l1 = l2.
Proof.
  intros X x. induction l1; intros; split; intros; inversion H; reflexivity.
Qed.


(* Replaced by functionality in SplitCutList    
Theorem split_list'_preserves_list' : forall (X: Type) (b: nat) (l l1 l2 l3: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list' b l3 l = ((rev l3) ++ l1, l2).
Proof. 
  induction b. 
  Case "b = 0". intros.
    simpl. apply length_0_impl_nil in H. subst. simpl. rewrite app_nil_r. 
    reflexivity.
  Case "b = S b". intros.
    destruct l.
    SCase "l = []".
      apply app_length_le_l1 in H0. simpl in H0. rewrite H in H0. inversion H0.
    SCase "l = x::l".
      simpl. destruct l1. simpl in H. inversion H.
      rewrite <- app_comm_cons in H0. inversion H0. rewrite H3.
      simpl. rewrite rev_app_cons. apply IHb.
      simpl in H. inversion H. reflexivity. apply H3.
Qed.  

Theorem split_list'_preserves_list : forall (X: Type) (b: nat) (l l1 l2: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list' b [] l = (l1, l2).
Proof.
  intros.
  replace (l1) with (rev [] ++ l1) by reflexivity.
  apply split_list'_preserves_list'; assumption.
Qed.

Theorem split_list_preserves_list : forall (X: Type) (b: nat) (l l1 l2: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list b l = (l1, l2).
Proof.
  intros. unfold split_list. apply split_list'_preserves_list; assumption.
Qed.

Theorem split_list'_preserves_lists : forall (X: Type) (b: nat) (l l1 l2 l3: list X),
   split_list' b l3 l = ((rev l3)++l1, l2) -> l = l1 ++ l2 /\ length l1 = b.
Proof.
  intros. generalize dependent l3.
  induction b.
  Case "b = 0".
    intros. simpl in H.
    inversion H. 
    symmetry in H1. apply app_list_eq_list_list in H1.
    subst.
    simpl.
    split; reflexivity.
  Case "b = S b".
    admit.
Admitted.

Theorem split_list_preserves_lists : forall (X: Type) (b: nat) (l l1 l2: list X),
   split_list b l = (l1, l2) -> l = l1 ++ l2 /\ length l1 = b.
Proof.
  intros.
  unfold split_list in H. replace (l1) with ((rev [])++l1) in H by reflexivity.
  apply split_list'_preserves_lists in H. apply H.
Qed.
*)


Lemma all_keys_elim_cons : forall (X: Type) (k1 k2: nat) (v1 v2: X) (l: list (nat*X)),
  above k1 k2 -> all_keys X (above k1) ((k1, v1) :: l) -> all_keys X (above k1) ((k1, v1) :: (k2, v2) :: l).
Proof.
  intros.
  inversion H0.
  inversion H3. 
  repeat constructor; assumption.
  repeat constructor; assumption.
Qed.

Lemma all_values_single : forall (X: Type) (P: X -> Prop) (x: X) (n: nat) (l1 l2: list (nat * X)),
  all_values X P (l1 ++ (n, x) :: l2) -> P x.
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl in H. inversion H. apply H4.
  Case "l1 = a::l1".
    rewrite <- app_comm_cons in H. inversion H. 
    apply IHl1.
      apply H2.
Qed.

(**
  key_at_index proofs
**)

Lemma key_at_index_0none_impl_empty: forall (X: Type) l,
  @key_at_index X 0 l = None -> l = [].
Proof. 
  intros. unfold key_at_index in H. destruct l. reflexivity. destruct p. inversion H.
Qed.



