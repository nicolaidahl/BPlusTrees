Require Export bplustree.

Example kvl_sorted_empty : @kvl_sorted nat [].
Proof. apply kvl_sorted_0. Qed.
Example kvl_sorted_single : kvl_sorted [(1, 1)].
Proof. apply kvl_sorted_1. Qed.
Example kvl_sorted_two : kvl_sorted [(1, 1), (2, 2)].
Proof. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. Qed.
Example kvl_sorted_two_WRONG : kvl_sorted [(2, 2), (1, 1)] -> False.
Proof. unfold not. intro. inversion H. inversion H6. Qed.

Theorem insert_preserves_sort : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> kvl_sorted (insert_into_list k v l).
Proof.
  intros. induction l. 
  Case "l = []". simpl. apply kvl_sorted_1.
  Case "l = a::l". simpl. destruct a. remember (ble_nat k n) as klen. destruct klen.
    SCase "k <= n". remember (beq_nat k n) as keqn. destruct keqn.
      SSCase "k = n". symmetry in Heqkeqn. apply beq_nat_true_iff in Heqkeqn. rewrite Heqkeqn. 
        destruct l. apply kvl_sorted_1. destruct p. inversion H.
        apply kvl_sorted_cons. apply H2. apply H6.
      
      SSCase "k != n". apply kvl_sorted_cons. apply H. 
                       symmetry in Heqklen. apply ble_nat_true in Heqklen. 
                       symmetry in Heqkeqn. apply beq_nat_false_iff in Heqkeqn.
                       apply blt_nat_true. omega.
    SCase "k > n". 
      
      inversion H. subst. compute. apply kvl_sorted_cons. apply kvl_sorted_1. 
      apply blt_nat_true. symmetry in Heqklen. apply ble_nat_false in Heqklen. omega.
      subst. unfold insert_into_list.
    admit.
Admitted.

Theorem insert_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  search_leaf k (insert_into_list k v l) = Some v. 
Proof.
  intros. induction l.
  Case "l = []". simpl. rewrite <- beq_nat_refl. reflexivity.
  Case "l = a::l".  simpl. destruct a. remember (ble_nat k n) as keq. destruct keq.
    rewrite <- Heqkeq.