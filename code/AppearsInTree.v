Require Export AppearsInKVL.
Require Export InductiveDataTypes.
Require Export BPlusTree.
Require Export ValidBPlusTree.
Require Export SortingProofs.
Require Export FindSubtreeProofs.

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

Lemma appears_in_tree_when_appears_in_last_subtree: forall (X: Type) (b k k1 k2: nat) (t1 t2: bplustree b X) (l1: list (nat * bplustree b X)),
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

Lemma appears_in_known_subtree: forall {X:Type} b n1 k n2 t1 t2 kpl kpl', 
  kpl = bptNode b X ((n1, t1) :: (n2, t2) :: kpl') ->
  n1 <= k < n2 ->
  appears_in_tree k (kpl) ->
  appears_in_tree k t1.
Proof.
  intros. induction H1; inversion H; subst; try (exfalso; omega).
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
  intros. induction H2; inversion H; subst; try (exfalso; omega).
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

Lemma appears_in_tree_two_last: forall {X: Type} b n1 n2 t1 t2 k,
  k >= n2 ->
  appears_in_tree k (bptNode b X [(n1, t1), (n2, t2)]) ->
  appears_in_tree k t2.
Proof. 
  intros. remember (bptNode b X [(n1, t1), (n2, t2)]). destruct H0. inversion Heqb0.
  inversion Heqb0. subst. assumption. inversion Heqb0. subst. exfalso. omega.
  inversion Heqb0.
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
	    apply find_subtree_one_impl_found in H1. destruct H1. rewrite <- H3. assumption.  
	    right. assumption. right. assumption. assumption. assumption.
	  SCase "kpl = p :: kpl".
	    destruct p.	    
	    apply IHkpl. apply list_tail_is_sorted in H. assumption. 
	    destruct Heqloc.
	      apply appears_in_tree_before_kpl_start_false in H0; try assumption. inversion H0.
	      eapply appears_in_later_subtree in H0. apply H0. reflexivity.  assumption. assumption.
	    eapply find_subtree_later in Heqloc. apply Heqloc. apply H. apply H1.
Qed.
  
(* Informal: We know k appears in the subtree that find_subtree returns, so
   * when appears_in_tree k parent tries to identify the subtree, it will find
   * the same as find_subtree, and because it exists in the subtree, it must also
   * exists in the parent tree *)
Lemma appears_in_tree_when_appears_in_subtree_and_found: forall (X: Type) (b k key: nat) (parent subtree: bplustree b X) (kpl: list (nat * bplustree b X)),
  2 <= length kpl ->
  kvl_sorted kpl ->
  parent = bptNode b X kpl ->
  find_subtree k kpl = Some (key, subtree) ->
  appears_in_tree k subtree ->

  appears_in_tree k parent.
Proof.
  intros.
  rewrite H1.
  assert (key <= k).
    apply find_subtree_returns_a_lesser_key in H2. assumption. omega.
  assumption.
  apply find_subtree_impl_kpl_app in H2.
  do 2 destruct H2.
  inversion H2. clear H2.
  destruct witness0.
  Case "witness0 = []".
    destruct witness.
    SCase "witness = []".
      simpl in H5. rewrite H5 in H. simpl in H. exfalso. omega.
    SCase "witness = p::witness".
      destruct p.
      rewrite <- app_comm_cons in H5.
      rewrite H5.
      rewrite H5 in H0.
      apply appears_in_tree_when_appears_in_last_subtree; assumption.
  Case "witness = p::witness".
    destruct p.
    inversion H6. inversion H2.
    do 3 destruct H2.
    inversion H2. clear H2. inversion H7. subst.
    apply appears_in_tree_when_appears_in_subtree; try assumption.
      omega.
Qed.

Lemma not_appears_in_subtree_when_not_appears_in_tree_and_found : forall (X: Type) (b k key: nat) (child: bplustree b X) (kpl: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  ~appears_in_tree k (bptNode b X kpl) ->
  find_subtree k kpl = Some(key, child) ->
  ~appears_in_tree k child.
Proof.
  intros.
  inversion H.
  unfold not.
  intro.
  apply H0.
  apply appears_in_tree_when_appears_in_subtree_and_found with (key := key) (subtree := child) (kpl := kpl);
            try assumption; try reflexivity.
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


  