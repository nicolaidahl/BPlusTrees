Require Export AppearsInKVL.
Require Export InductiveDataTypes.
Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.

Theorem appears_search_works : forall (b: nat) (X: Type) (t t1: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> 
  appears_in_tree k t -> 
  search k t = Some(v).
Proof.
  intros. induction H0. Admitted.
  

  
Lemma appears_in_split_node_appears_in_lists: forall {X: Type} b k n left right, 
  kvl_sorted (left ++ right) ->
  key_at_index 0 right = Some n ->
  appears_in_kvl k left \/ appears_in_kvl k right ->
  appears_in_tree k (bptNode b X [(0, bptLeaf b X left), (n, bptLeaf b X right)]).
Proof.
  intros. destruct H1. 
  Case "Left hand side".
    apply ait_node_here. apply ait_leaf. assumption. destruct right.
    simpl in H0. inversion H0. inversion H0. destruct p. inversion H3. subst.
    apply appears_in_kvl_app in H1. do 3 destruct H1. subst. 
    rewrite <- app_assoc in H. apply kvl_sorted_app with (l1:=witness) in H. destruct H.
    apply kvl_sorted_key_across_app in H1. omega.
  Case "Right hand side".
    apply ait_node_later. apply ait_node_one. apply ait_leaf. assumption. 
    SCase "n <=".
      inversion H0. destruct right. inversion H3. destruct p. inversion H3. subst. remember (beq_nat n k).
      destruct b0. symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. omega.
      apply appears_cons in H1. apply appears_in_kvl_app in H1. do 3 destruct H1. subst.
      apply kvl_sorted_app with (l1:=left) in H. inversion H. 
      apply kvl_sorted_key_across_app in H2.  omega. symmetry in Heqb0. 
      apply beq_nat_false in Heqb0. omega.
    SCase "< n".
    inversion H0. destruct right. inversion H3. destruct p. inversion H3. subst.
    remember (beq_nat n k).
    destruct b0. symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. omega.
    apply appears_cons in H1. apply appears_in_kvl_app in H1. do 3 destruct H1. subst.
    apply kvl_sorted_app with (l1:=left) in H. inversion H. 
    apply kvl_sorted_key_across_app in H2. omega. symmetry in Heqb0. 
    apply beq_nat_false in Heqb0. omega.
Qed.
  
  
  
  
  
  
  