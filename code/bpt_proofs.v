Require Export bplustree.

Example kvl_sorted_empty : @kvl_sorted nat [].
Proof. apply kvl_sorted_0. Qed.
Example kvl_sorted_single : kvl_sorted [(1, 1)].
Proof. apply kvl_sorted_1. Qed.
Example kvl_sorted_two : kvl_sorted [(1, 1), (2, 2)].
Proof. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. Qed.
Example kvl_sorted_two_WRONG : kvl_sorted [(2, 2), (1, 1)] -> False.
Proof. unfold not. intro. inversion H. inversion H6. Qed.

Lemma sort_ignores_value : forall (X: Type) (k: nat) (v1 v2: X) (l: list (nat * X)),
  kvl_sorted ((k,v1)::l) -> kvl_sorted((k, v2)::l).
Proof.
  intros. inversion H. apply kvl_sorted_1.
  apply kvl_sorted_cons. apply H2. apply H4.
Qed.

Theorem insert_preserves_sort : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> kvl_sorted (insert_into_list k v l).
Proof.
  intros. induction H.
  Case "kvl_sorted_0". simpl. apply kvl_sorted_1.
  Case "kvl_sorted_1". simpl. remember (ble_nat k n) as klen. destruct klen.
    SCase "k <= n". remember (beq_nat k n) as keqn. destruct keqn.
      SSCase "k = n". apply kvl_sorted_1.
      SSCase "k != n". apply kvl_sorted_cons. apply kvl_sorted_1.
      				   symmetry in Heqklen. apply ble_nat_true in Heqklen. 
                       symmetry in Heqkeqn. apply beq_nat_false_iff in Heqkeqn.
                       apply blt_nat_true. omega.
    SCase "k > n". apply kvl_sorted_cons. apply kvl_sorted_1.
    	symmetry in Heqklen. apply ble_nat_false in Heqklen.
    	apply blt_nat_true. omega.
  Case "kvl_sorted_cons". 
    simpl. remember (ble_nat k n1) as klen1. destruct klen1.
    SCase "k <= n1". remember (beq_nat k n1) as keqn1. destruct keqn1.
      apply kvl_sorted_cons. apply H. apply blt_nat_true in H0.
      				   symmetry in Heqklen1. apply ble_nat_true in Heqklen1. 
                       symmetry in Heqkeqn1. apply beq_nat_true_iff in Heqkeqn1.
                       apply blt_nat_true. omega.
      apply kvl_sorted_cons. apply kvl_sorted_cons. apply H. apply H0.
         apply blt_nat_true in H0.
         symmetry in Heqklen1. apply ble_nat_true in Heqklen1. 
         symmetry in Heqkeqn1. apply beq_nat_false_iff in Heqkeqn1.
         apply blt_nat_true. omega.
    SCase "k > n1".  remember (ble_nat k n2) as klen2. destruct klen2.
      SSCase "k <= n2". remember (beq_nat k n2) as keqn2. destruct keqn2.
        SSSCase "k = n2".
          apply kvl_sorted_cons. apply blt_nat_true in H0. 
          symmetry in Heqklen1. apply ble_nat_false in Heqklen1.
          symmetry in Heqklen2. apply ble_nat_true in Heqklen2.
          symmetry in Heqkeqn2. apply beq_nat_true_iff in Heqkeqn2. subst.
          eapply sort_ignores_value. apply H. apply blt_nat_true in H0.
          symmetry in Heqklen1. apply ble_nat_false in Heqklen1.
          symmetry in Heqklen2. apply ble_nat_true in Heqklen2.
          symmetry in Heqkeqn2. apply beq_nat_true_iff in Heqkeqn2.
          apply blt_nat_true. omega.
        SSSCase "k != n2". 
          apply kvl_sorted_cons. apply kvl_sorted_cons. apply H.
          apply blt_nat_true in H0. 
          symmetry in Heqklen1. apply ble_nat_false in Heqklen1.
          symmetry in Heqklen2. apply ble_nat_true in Heqklen2.
          symmetry in Heqkeqn2. apply beq_nat_false_iff in Heqkeqn2.
          apply blt_nat_true. omega.
          apply blt_nat_true in H0. 
          symmetry in Heqklen1. apply ble_nat_false in Heqklen1.
          symmetry in Heqklen2. apply ble_nat_true in Heqklen2.
          symmetry in Heqkeqn2. apply beq_nat_false_iff in Heqkeqn2.
          apply blt_nat_true. omega.
     SSCase "k > n2".
       admit.
Admitted.

Theorem insert_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  search_leaf k (insert_into_list k v l) = Some v. 
Proof.
  intros. induction l.
  Case "l = []". simpl. rewrite <- beq_nat_refl. reflexivity.
  Case "l = a::l".  simpl. destruct a. remember (ble_nat k n) as keq. destruct keq.
    rewrite <- Heqkeq.