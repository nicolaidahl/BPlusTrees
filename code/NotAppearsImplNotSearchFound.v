Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.
Require Export AppearsInKVL.
Require Export HeightProofs.
Require Export InsertProofs.

Theorem not_appears_leaf_impl_search_leaf_not_found: forall (X: Type) k (l: list (nat *X)),
  kvl_sorted l ->
  ~ appears_in_kvl k l -> 
  search_leaf k l = None.
Proof.
  intros. induction l. simpl. reflexivity.
  destruct a.  
  assert ( ~ appears_in_kvl k ((n, x) :: l)) by assumption.
  apply not_appears_in_kvl_key_not_equal with (l1:=[]) in H1.
  simpl.
  assert (beq_nat n k = false).
    apply beq_nat_false_iff.
  omega. rewrite H2. 
  apply IHl.
  apply list_tail_is_sorted in H. assumption.
  apply not_appears_in_kvl_impl_remove_element with (l1:=[]) in H0.
  assumption.
Qed.



Theorem not_appears_impl_search'_not_found : forall (X: Type) (b sk: nat) 
                                             (t: bplustree b X),
  valid_bplustree b X t ->
  ~ appears_in_tree sk t ->
  search' (height t) sk t = None.
Proof.
  intros. remember (height t) as counter. 
  generalize dependent b. generalize dependent sk.
  induction counter; intros.
  Case "height t = 0".
    simpl. destruct t. eapply not_appears_leaf_impl_search_leaf_not_found. 
    inversion H. assumption.
    unfold not in H0. unfold not. intro. apply H0. apply ait_leaf. assumption.
    reflexivity.
  Case "height t = S height t".
    inversion H.
    SCase "bptLeaf".
      subst. simpl in Heqcounter. inversion Heqcounter.
    SCase "bptNode".
      simpl.
      remember (find_subtree sk kpl).
      destruct o.
      SSCase "find_subtree = Some p". 
        symmetry in Heqo. destruct p.
        assert (find_subtree sk kpl = Some (n, b0)) by assumption.
        (* Our goal here is to find all the requirements for using IHcounter
         * on the tree b0. *)
        assert (valid_bplustree b X b0).
          apply find_subtree_impl_kpl_app in H10.
          do 2 destruct H10. inversion H10. clear H10.
          rewrite H11 in H5.
          apply all_values_single in H5.
          apply valid_sub_bplustree_impl_valid_bplustree in H5.
          apply H5.
        assert (~ appears_in_tree sk b0).
          unfold not. unfold not in H0. intro.
          apply not_appears_in_subtree_when_not_appears_in_tree_and_found in Heqo.
          unfold not in Heqo. apply Heqo in H12. assumption.
          rewrite <- H9 in H. assumption.
          rewrite <- H9 in H0. assumption.
        assert (counter = height b0).
          apply find_subtree_impl_kpl_app in H10.
          do 2 destruct H10. inversion H10. clear H10.
          apply height_of_parent_one_bigger in H13.
          rewrite H9 in H13.
          omega.
          apply H6.
          
        apply IHcounter; assumption. reflexivity.
Qed.



Theorem not_appears_impl_search_not_found: forall (b: nat) (X: Type) (t: bplustree b X) (k: nat),
  valid_bplustree b X t -> 
  ~ appears_in_tree k t -> 
  search k t = None.
Proof. 
  intros. unfold search.
  apply not_appears_impl_search'_not_found; try assumption.
Qed.
