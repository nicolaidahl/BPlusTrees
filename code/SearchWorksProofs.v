Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.
Require Export AppearsInKVL.
Require Export HeightProofs.
Require Export InsertProofs.
Require Export KvAppearsInTree.

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

Theorem search_leaf_works : forall (X: Type) (k: nat) (v: X) (kvl: list (nat * X)),
  kvl_sorted kvl ->
  kv_appears_in_kvl k v kvl -> search_leaf k kvl = Some v.
Proof.
  intros.
  apply kv_appears_in_kvl_app in H0.
  do 2 destruct H0.
  rewrite H0.
  apply search_leaf_works_app.
  rewrite <- H0.
  assumption.
Qed.


Theorem appears_search'_works : forall (X: Type) (counter b sk: nat) (sv: X) (t: bplustree b X),
  valid_bplustree b X t ->
  kv_appears_in_tree sk sv t ->
  counter = (height t) ->
  search' counter sk t = Some(sv).
Proof.
  induction counter.
  Case "counter = 0".
    intros.
    inversion H. 
    SCase "bptLeaf". 
      subst. inversion H0.
      apply search_leaf_works; assumption.
    SCase "bptNode".
      subst. simpl in H1.
      destruct kpl.
      simpl in H3. exfalso. omega.
      destruct p. inversion H1.
  Case "counter = S counter".
    intros.
    inversion H.
    SCase "bptLeaf".
      subst. simpl in H1. inversion H1.
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
          apply find_subtree_impl_kpl_app in H11.
          do 2 destruct H11. inversion H11. clear H11.
          rewrite H12 in H6.
          apply all_values_single in H6.
          apply valid_sub_bplustree_impl_valid_bplustree in H6.
          apply H6.
        assert (kv_appears_in_tree sk sv b0).
          apply kv_appears_in_subtree_when_appears_in_tree_and_found with (v := sv) in Heqo.
          apply Heqo. assumption.
          rewrite H10. assumption.
        assert (counter = height b0).
          apply find_subtree_impl_kpl_app in H11.
          do 2 destruct H11. inversion H11. clear H11.
          apply height_of_parent_one_bigger in H14.
          rewrite H10 in H14.
          omega.
          apply H7.
          
        apply IHcounter; assumption.
      SSCase "find_subtree = None".
        rewrite <- H10 in H. 
        apply find_subtree_finds_a_subtree with (sk := sk) in H.
        do 2 destruct H. rewrite H in Heqo.
        inversion Heqo.
Qed.
    
Theorem appears_search_works : forall (b: nat) (X: Type) (v: X) (t: bplustree b X) (k: nat),
  valid_bplustree b X t -> 
  kv_appears_in_tree k v t -> 
  search k t = Some(v).
Proof.
  intros.
  unfold search.
  remember (height t) as counter.
  apply appears_search'_works; assumption.
Qed.



Theorem not_appears_search_works: forall (b: nat) (X: Type) (t: bplustree b X) (k: nat),
  valid_bplustree b X t -> 
  ~ appears_in_tree k t -> 
  search k t = None.
Proof. Admitted.




