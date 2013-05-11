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

Lemma appears_in_known_subtree: forall {X:Type} b n1 k n2 t1 t2 kpl kpl', 
  kpl = bptNode b X ((n1, t1) :: (n2, t2) :: kpl') ->
  n1 <= k < n2 ->
  appears_in_tree k (kpl) ->
  appears_in_tree k t1.
Proof.
  intros. induction H1; inversion H; subst; try omega.
  Case "ait_here".
    assumption.
Qed.

Lemma appears_in_later_subtree: forall {X:Type} b n1 k n2 n3 t1 t2 t3 kpl kpl', 
  kpl = bptNode b X ((n1, t1) :: (n2, t2) :: (n3, t3) :: kpl') ->
  kvl_sorted ((n1, t1) :: (n2, t2) :: (n3, t3) :: kpl') ->
  k >= n2 ->
  appears_in_tree k kpl ->
  appears_in_tree k (bptNode b X ((n2, t2) :: (n3, t3) :: kpl')).
Proof. 
  intros. induction H2; inversion H; subst. 
  omega.
  assumption.
Qed.


Lemma appears_in_tree_before_kpl_start_false: forall {X:Type} b n k t kpl, 
  n > k ->
  kvl_sorted ((n, t) :: kpl) ->
  appears_in_tree k (bptNode b X ((n, t) :: kpl)) ->
  False.
Proof.
  intros. remember (bptNode b X ((n, t) :: kpl)). destruct H1; inversion Heqb0; subst.
  apply kvl_sorted_key_across_app with (l1:=[])(l2:=[]) in H0. omega. omega.
  apply kvl_sorted_key_across_app with (k1:=n)(v1:=t)(k2:=k1)(v2:=v1)(l1:=[])(l2:=(k2, v2)::l) in H0. 
  omega.
Qed.

Lemma find_subtree_finds_a_subtree' : forall (X: Type) (b sk k0: nat) (t0: bplustree b X) (l: list (nat * bplustree b X)),
  2 <= length ((k0, t0)::l) ->
  k0 <= sk ->
  exists key, exists child, find_subtree sk ((k0, t0)::l) = Some (key, child).
Proof.
  intros. generalize dependent k0. generalize dependent t0.
  induction l.
  Case "l = []".
    intros.
    simpl in H. exfalso. omega.
  Case "l = a::l".
    intros.
    destruct a.
    destruct l.
    SCase "l = [_, _]".
      assert (ble_nat k0 sk = true) by (apply ble_nat_true; assumption).
      simpl. rewrite H1. simpl.
      remember (blt_nat sk n).
      destruct b1. exists k0. exists t0. reflexivity.
      remember (ble_nat n sk).
      destruct b1.
      exists n. exists b0. reflexivity.
      symmetry in Heqb1. apply blt_nat_false in Heqb1.
      symmetry in Heqb0. apply ble_nat_false in Heqb0. 
      exfalso. omega.
    SCase "l = _::_::p::l".
      simpl. simpl in IHl.
      remember (ble_nat k0 sk && blt_nat sk n) as here.
      destruct here.
      exists k0. exists t0. reflexivity. 
      apply IHl. omega.
      symmetry in Heqhere. apply andb_false_iff in Heqhere.
      inversion Heqhere.
      apply ble_nat_false in H1. exfalso. omega.
      apply blt_nat_false in H1. omega.
Qed.

Lemma find_subtree_later: forall {X: Type} b n1 n2 k t1 t2 kpl key subtree,
  n1 > k \/ k >= n2 ->
  kvl_sorted((n1, t1) :: (n2, t2) :: kpl) ->
  @find_subtree X b k ((n1, t1) :: (n2, t2) :: kpl) = Some (key, subtree) ->
  @find_subtree X b k ((n2, t2) :: kpl) = Some (key, subtree).
Proof.
  intros. destruct H. admit.
  simpl in H1. assert (~ (k < n2)). omega. apply blt_nat_false in H2.
  assert (ble_nat n1 k && blt_nat k n2 = false). unfold andb. rewrite H2. 
    destruct (ble_nat n1 k). reflexivity. reflexivity.
   rewrite H3 in H1. apply H1.
Qed.

Lemma appears_in_tree_two_last: forall {X: Type} b n1 n2 t1 t2 k,
  k >= n2 ->
  appears_in_tree k (bptNode b X [(n1, t1), (n2, t2)]) ->
  appears_in_tree k t2.
Proof. 
  intros. remember (bptNode b X [(n1, t1), (n2, t2)]). destruct H0. inversion Heqb0.
  inversion Heqb0. subst. assumption. inversion Heqb0. subst.  omega.
  inversion Heqb0.
Qed.
  

Lemma find_subtree_one_impl_found: forall {X: Type} b k n t key subtree,
  k >= n ->
  @find_subtree X b k [(n, t)] = Some (key, subtree) ->
  t = subtree.
Proof.
  intros. simpl in H0. destruct (ble_nat n k). inversion H0. reflexivity. inversion H0.
Qed.


(* Informal: We know k appears in the parent tree, and we know that find_subtree
 * returns the subtree when searching for k, so hence k must also appear in the
 * subtree *)
Lemma appears_in_subtree_when_appears_in_tree_and_found: 
    forall (X: Type) (b k key: nat) 
    (subtree: bplustree b X) (kpl: list (nat * bplustree b X)),
  
  kvl_sorted(kpl) ->
  appears_in_tree k (bptNode b X kpl) ->
  find_subtree k kpl = Some (key, subtree) ->
  
  appears_in_tree k subtree.
Proof.
  intros. induction kpl. 
  Case "kpl = []".
	  simpl in H0. inversion H0. 
  Case "kpl = a :: kpl".
  	  destruct a. destruct kpl. 
  	    inversion H0. 
  	    destruct p. remember (ble_nat n k && blt_nat k n0) as loc. destruct loc. 
  	      unfold find_subtree in H1. rewrite <- Heqloc in H1. inversion H1. 
	      symmetry in Heqloc. unfold andb in Heqloc. 
	      apply ble_and_blt_true in Heqloc. eapply appears_in_known_subtree in H0. 
	      apply H0. rewrite H4. reflexivity. assumption. 
	  symmetry in Heqloc. apply ble_and_blt_false in Heqloc.
	  destruct kpl.
	  SCase "kpl = []".
	    destruct Heqloc.
	    apply appears_in_tree_before_kpl_start_false in H0. inversion H0.
	    assumption. assumption.
	    apply appears_in_tree_two_last in H0.  apply find_subtree_later in H1. 
	    apply find_subtree_one_impl_found in H1. rewrite <- H1. assumption.  
	    assumption. right. assumption. assumption. assumption.
	  SCase "kpl = p :: kpl".
	    destruct p.	    
	    apply IHkpl. apply list_tail_is_sorted in H. assumption. 
	    destruct Heqloc.
	      apply appears_in_tree_before_kpl_start_false in H0; try assumption. inversion H0.
	      eapply appears_in_later_subtree in H0. apply H0. reflexivity.  assumption. assumption.
	    eapply find_subtree_later in Heqloc. apply Heqloc. apply H. apply H1.
Qed.
  




  
Lemma appears_in_tree_when_appears_in_subtree_and_found: forall (X: Type) (b k key: nat) (parent subtree: bplustree b X) (kpl: list (nat * bplustree b X)),
  parent = bptNode b X kpl ->
  find_subtree k kpl = Some (key, subtree) ->
  appears_in_tree k subtree ->

  appears_in_tree k parent.
Proof.
  (* Informal: We know k appears in the subtree that find_subtree returns, so
   * when appears_in_tree k parent tries to identify the subtree, it will find
   * the same as find_subtree, and because it exists in the subtree, it must also
   * exists in the parent tree *)
  admit.
Admitted.

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
  