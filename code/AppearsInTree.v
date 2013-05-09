Require Export AppearsInKVL.
Require Export InductiveDataTypes.
Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.

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
    apply ait_node_last. apply ait_leaf. assumption. 
    SCase "n <=".
      inversion H0. destruct right. inversion H3. destruct p. inversion H3. subst. remember (beq_nat n k).
      destruct b0. symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. omega.
      apply appears_cons in H1. apply appears_in_kvl_app in H1. do 3 destruct H1. subst.
      apply kvl_sorted_app with (l1:=left) in H. inversion H. 
      apply kvl_sorted_key_across_app in H2.  omega. symmetry in Heqb0. 
      apply beq_nat_false in Heqb0. omega.
Qed.

Lemma appears_in_tree_when_appears_in_subtree: forall (X: Type) (b k k1 k2: nat) (t1 t2: bplustree b X) (l1 l2: list (nat * bplustree b X)),
  appears_in_tree k t1 -> 
  k1 <= k < k2 ->
  kvl_sorted (l1 ++ (k1, t1) :: (k2, t2)::l2) ->
  appears_in_tree k (bptNode b X (l1 ++ (k1, t1) :: (k2, t2)::l2)).
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl.
   apply ait_node_here; assumption.
     destruct a. rewrite <- app_comm_cons.
     destruct l1. 
       simpl.
       apply ait_node_later. apply IHl1. 
         simpl. simpl in H1. apply list_tail_is_sorted in H1. apply H1.
         omega.
       rewrite <- app_comm_cons. destruct p.
       destruct l1.
         simpl. apply ait_node_later. simpl in IHl1. apply IHl1. 
           simpl in H1. apply list_tail_is_sorted in H1. apply H1.
           simpl in H1. inversion H1. inversion H4.
           apply blt_nat_true in H15. omega.
           
         rewrite <- app_comm_cons. destruct p.
         apply ait_node_later. apply IHl1.
           apply list_tail_is_sorted in H1. apply H1.
           simpl in H1.
           inversion H1.
           apply kvl_sorted_key_across_app with (l1 := ((n1,b2)::l1)) in H4.
           omega.
Qed.

Lemma appears_in_tree_when_appears_in_last_subtree: forall (X: Type) (b k k1 k2: nat) (t1 t2: bplustree b X) (l1 l2: list (nat * bplustree b X)),
  appears_in_tree k t1 -> 
  k1 <= k ->
  kvl_sorted ((k2,t2)::l1 ++ [(k1, t1)]) ->
  appears_in_tree k (bptNode b X ((k2,t2)::l1 ++ [(k1, t1)])).
Proof.
  intros. generalize dependent k2. generalize dependent t2.
  induction l1.
  Case "l1 = []".
    intros.
    simpl.
    apply ait_node_last; assumption.
  Case "l1 = a::l1". destruct a.
    intros.
    destruct l1.
      simpl.
      apply ait_node_later. apply ait_node_last; assumption.
      simpl in H1.
      inversion H1. inversion H4.
      apply blt_nat_true in H15. omega.
      destruct p.
      repeat rewrite <- app_comm_cons.
      apply ait_node_later.
      apply IHl1.
      simpl in H1. simpl. apply list_tail_is_sorted in H1. apply H1.
      
      simpl in H1. apply list_tail_is_sorted in H1.
      apply kvl_sorted_key_across_app with (l1 := ((n0, b1)::l1)) in H1.
      omega.
Qed.    
  
(*
Lemma key_valid_when_appears_and_between : forall (X: Type) (b k1 k2 sk: nat) (t: bplustree b X), 
  appears_in_tree sk t ->
  all_keys X (between k1 k2) (inorder t)
  -> k1 <= sk < k2.
Proof.
  admit.
Admitted.
  
Lemma appears_in_valid_tree_when_appears_in_subtree : forall (X: Type) (b k sk: nat) (t: bplustree b X) (l1 l2: list (nat * bplustree b X)), 
  valid_bplustree b X (bptNode b X (l1++(k,t)::l2)) ->
  appears_in_tree sk t ->
  appears_in_tree sk (bptNode b X (l1++(k,t)::l2)).
Proof.
  intros.
  inversion H.
  induction l1.
    simpl in *.
    inversion H8.
    apply ait_node_here; try assumption.
    eapply key_valid_when_appears_and_between.
      apply H0.
      apply H11.
    admit.
*) 
  