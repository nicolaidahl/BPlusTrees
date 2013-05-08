Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.
Require Export AppearsInKVL.
Require Export HeightProofs.

Theorem search_leaf_works_app : forall (X: Type) (k: nat) (v: X) (l1 l2: list (nat * X)), 
  kvl_sorted (l1 ++ (k, v) :: l2) ->
  search_leaf k (l1 ++ (k, v) :: l2) = Some v.
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl. rewrite <- beq_nat_refl.
    reflexivity.
  Case "l1 = a::l1".
    simpl.
    destruct a.
    remember (beq_nat n k) as eq.
    destruct eq.
    SCase "not here".
      apply kvl_sorted_key_across_app in H.
      symmetry in Heqeq. apply beq_nat_true_iff in Heqeq.
      apply ex_falso_quodlibet. omega.
    SCase "later".
      apply IHl1.
      rewrite <- app_comm_cons in H.
      apply list_tail_is_sorted in H.
      assumption.
Qed.

Theorem search_leaf_works : forall (X: Type) (k: nat) (kvl: list (nat * X)),
  kvl_sorted kvl ->
  appears_in_kvl k kvl -> exists v, search_leaf k kvl = Some v.
Proof.
  intros.
  apply appears_in_kvl_app in H0.
  do 3 destruct H0.
  exists witness1.
  rewrite H0.
  apply search_leaf_works_app.
  rewrite <- H0.
  assumption.
Qed.


Theorem appears_search_works : forall (b: nat) (X: Type) (t: bplustree b X) (k: nat),
  valid_bplustree b X t -> 
  appears_in_tree k t -> 
  exists v, search k t = Some(v).
Proof.
  intros.
  unfold search.
  induction H0; inversion H.
  Case "leaf".
    simpl.
    apply search_leaf_works.
    SCase "l sorted".
      assumption.
    SCase "appears in l".
      assumption.
  Case "node last".
    replace (height (bptNode b X [(k1,v1), (k2,v2)])) with (S (height v2)).
    simpl.
    remember (ble_nat k1 k && blt_nat k k2) as here.
    destruct here.
      symmetry in Heqhere. apply andb_true_iff in Heqhere. inversion Heqhere.
      apply blt_nat_true in H11. exfalso. omega.
    apply IHappears_in_tree.
    inversion H6.
    assert (valid_bplustree b X v2).
      inversion H12.
      apply valid_sub_bplustree_impl_valid_bplustree in H19. assumption.
    assumption.
    apply height_of_parent_one_bigger with (l1 := [(k1, v1)]) (l2 := []) (k := k2). reflexivity. apply H7.    
  Case "node here".
    assert (height (bptNode b X ((k1, v1) :: (k2, v2) :: l)) = S (height v1)).
      symmetry. apply height_of_parent_one_bigger with (l1 := []) (l2 := (k2, v2)::l) (k := k1). reflexivity. assumption.
    assert (ble_nat k1 k && blt_nat k k2 = true).
      apply andb_true_iff; split; [apply ble_nat_true | apply blt_nat_true]; omega.
    simpl. rewrite H11.   
    apply IHappears_in_tree.
    assert (valid_bplustree b X v1).
      inversion H6.
      apply valid_sub_bplustree_impl_valid_bplustree in H16. assumption.
    assumption.
    
  Case "node later".
    destruct x.
    inversion H8. apply blt_nat_true in H16. subst.
    assert ((height (bptNode b X ((n, b0) :: (k1, v1) :: (k2, v2) :: l))) = (height (bptNode b X ((k1, v1) :: (k2, v2) :: l)))).
      rewrite height_cons. reflexivity.
      apply H.
      simpl in H5.
      constructor; try assumption; simpl; try omega.
      simpl in H4. 
      inversion H6. apply H11.
      inversion H7. apply H11.
      inversion H9. apply H17.
    rewrite H2.
    
    simpl.
    assert (ble_nat n k && blt_nat k k1 = false).
      apply andb_false_iff. right. apply blt_nat_false. omega.
    rewrite H10.
    
    simpl in IHappears_in_tree. apply IHappears_in_tree.
    clear IHappears_in_tree.
    inversion H6.
    constructor; try assumption.
    simpl. omega. 
    simpl. simpl in H5. omega.
    inversion H7. apply H20.
    inversion H9. apply H24.
Qed.