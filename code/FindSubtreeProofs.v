Require Export InductiveDataTypes.
Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export AppearsInKVL.



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

Lemma find_subtree_finds_a_subtree : forall (X: Type) (b sk: nat) (l: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X l) ->
  exists key, exists child, find_subtree sk l = Some (key, child).
Proof.
  intros.
  inversion H.
  destruct l.  simpl in H2. exfalso. omega.
  destruct p.
  simpl in H4. inversion H4.
  apply find_subtree_finds_a_subtree'.
    assumption.
    omega.
Qed.

Lemma find_subtree_before_head_None: forall {X: Type} {b: nat} n k t (kpl: list (nat * bplustree b X)),
  n > k -> kvl_sorted ((n, t) :: kpl) ->
  find_subtree k ((n, t) :: kpl) = None.
Proof.
  intros. generalize dependent n. generalize dependent t. induction kpl. intros.
  Case "kpl = []".
    simpl. assert (ble_nat n k = false). apply ble_nat_false.  omega.
    rewrite H1. reflexivity.
  Case "kpl = a :: kpl".
    intros. destruct a. simpl. 
    assert (ble_nat n k = false). apply ble_nat_false. omega.
    rewrite H1. simpl. apply IHkpl.  
    apply kvl_sorted_key_across_app with (l1:=[])(l2:=kpl) in H0. omega.
    apply list_tail_is_sorted in H0. assumption.
Qed.
  

Lemma find_subtree_later: forall {X: Type} b n1 n2 k t1 t2 (kpl: list (nat * bplustree b X)) key subtree,
  n1 > k \/ k >= n2 ->
  kvl_sorted((n1, t1) :: (n2, t2) :: kpl) ->
  find_subtree k ((n1, t1) :: (n2, t2) :: kpl) = Some (key, subtree) ->
  find_subtree k ((n2, t2) :: kpl) = Some (key, subtree).
Proof.
  intros. destruct H. 
  eapply find_subtree_before_head_None in H0. rewrite H0 in H1. inversion H1.
  assumption.
  simpl in H1. assert (~ (k < n2)). omega. apply blt_nat_false in H2.
  assert (ble_nat n1 k && blt_nat k n2 = false). unfold andb. rewrite H2. 
    destruct (ble_nat n1 k). reflexivity. reflexivity.
   rewrite H3 in H1. apply H1.
Qed.



Lemma find_subtree_one_impl_found: forall {X: Type} b k (n: nat) (t: bplustree b X) key subtree,
  key <= k \/ n <= k ->
  find_subtree k [(n, t)] = Some (key, subtree) ->
  n = key /\ t = subtree.
Proof.
  intros. simpl in H0. destruct (ble_nat n k). inversion H0. split. reflexivity. 
  reflexivity. inversion H0.
Qed.

Lemma find_subtree_impl_kpl_app : forall (X: Type) (b sk key: nat) (kpl: list (nat * bplustree b X)) (subtree: bplustree b X),
  find_subtree sk kpl = Some (key, subtree) ->
  
  exists l1, exists l2, kpl = l1 ++ (key, subtree)::l2
  /\
  (l2 = [] 
    \/
   exists k2, exists v2, exists l2', l2 = (k2,v2)::l2' /\ sk < k2).
Proof.
  intros.
  induction kpl.
  Case "kpl = []".
    simpl in H. inversion H.
  Case "kpl = a::kpl". destruct a.
    simpl in H.
    destruct kpl.
    SCase "kpl = [a]".
      remember (ble_nat n sk).
      destruct b1.
      SSCase "it was the last".
        inversion H.
        exists []. exists [].
        split. reflexivity.
        left. reflexivity.
      SSCase "it wasn't the last".
        inversion H.
    SCase "kpl = a::p::kpl". destruct p.
      remember (ble_nat n sk && blt_nat sk n0) as here.
      destruct here.
      SSCase "found here".
        inversion H.
        exists []. exists ((n0,b1)::kpl).
        split. reflexivity.
        right. exists n0. exists b1. exists kpl.
        split. reflexivity.
        symmetry in Heqhere. apply andb_true_iff in Heqhere.
        inversion Heqhere. apply blt_nat_true in H3. omega.
      SSCase "found later".
        apply IHkpl in H.
        do 2 destruct H.
        inversion H.
        exists ((n,b0)::witness). exists witness0.
        split. rewrite H0. reflexivity.
        apply H1.
Qed.

Lemma find_subtree_returns_a_lesser_key : forall (X: Type) (b sk key: nat) (child: bplustree b X) (l: list (nat * bplustree b X)),
  1 <= length l ->
  kvl_sorted l -> 
  find_subtree sk l = Some (key, child) ->
  key <= sk.
Proof.
  intros. induction H0.
  Case "kvl_sorted_0".
    inversion H.
  Case "kvl_sorted_1".
    compute in H. simpl in H1. remember (ble_nat n sk). destruct b0. inversion H1. subst.
    symmetry in Heqb0. apply ble_nat_true in Heqb0. omega. inversion H1.
  Case "kvl_sorted_cons".
    destruct lst.
    SCase "lst = []".
      simpl in H1. remember (ble_nat n1 sk). destruct b0. remember (blt_nat sk n2). destruct b0.
      simpl in H1. inversion H1. subst. symmetry in Heqb0. apply ble_nat_true in Heqb0. omega.
      simpl in H1. remember (ble_nat n2 sk). destruct b0. inversion H1. subst.
      symmetry in Heqb2. apply ble_nat_true in Heqb2. omega. inversion H1.
      simpl in H1. remember (ble_nat n2 sk). destruct b0. 
      symmetry in Heqb0. symmetry in Heqb1. 
      apply ble_nat_false in Heqb0. apply ble_nat_true in Heqb1. apply blt_nat_true in H2. omega.
      inversion H1.
    SCase "lst = p :: lst".
      destruct p. simpl in H1.
      remember (ble_nat n1 sk && blt_nat sk n2). destruct b1.
      SSCase "found first element".
        inversion H1. subst. symmetry in Heqb1. apply ble_and_blt_true in Heqb1. omega.
      SSCase "not in first element".
        apply IHkvl_sorted. simpl. omega.
        apply H1.
Qed.

  
  

Lemma find_subtree_impl_key_appears : forall (X: Type) (b k key: nat) 
                                      (kpl: list (nat * bplustree b X)) (subtree: bplustree b X), 
  find_subtree k kpl = Some (key, subtree) -> 
  appears_in_kvl key kpl.
Proof.
  intros. induction kpl. simpl in H. inversion H.
  destruct a. destruct kpl.
  Case "kpl = []".
    simpl in H. remember (ble_nat n k). destruct b1. inversion H. subst. 
    apply aik_here. inversion H.
  Case "kpl = a :: kpl".
    destruct p. simpl in H.
    remember (ble_nat n k && blt_nat k n0). destruct b2. inversion H. subst.
    apply aik_here. apply aik_later. apply IHkpl. apply H.
Qed.

Lemma kvl_sorted_k1_k2_impl_k2_later: forall {X: Type} (b:nat) k1 t1 k2 (l: list (nat*bplustree b X)),
  kvl_sorted ((k1, t1) :: l) ->
  appears_in_kvl k2 ((k1, t1) :: l) ->
  k1 <= k2.
Proof.
  intros. remember ((k1, t1) ::l) as kvl.
  induction H0.
    inversion Heqkvl.
    omega.
    inversion Heqkvl. subst.
    apply appears_in_kvl_app in H0.
    do 3 (destruct H0).
    rewrite H0 in H. 
    apply kvl_sorted_key_across_app in H.
    omega.
Qed.

Lemma find_subtree_now_or_later: forall {X: Type} (b:nat) sk k1 k2 t1 t2 
                                 (l: list(nat*bplustree b X)),
  kvl_sorted ((k1, t1) :: l) ->
  find_subtree sk ((k1, t1) :: l) = Some (k2, t2) ->
  k1 <= k2.
Proof.
  intros. remember ((k1, t1) :: l) as kpl.
  destruct kpl.
  Case "kpl = []".
    inversion Heqkpl.
  Case "kpl = a :: kpl".
    destruct p. inversion Heqkpl.
    apply find_subtree_impl_key_appears in H0. rewrite <- H2.
    eapply kvl_sorted_k1_k2_impl_k2_later. apply H. apply H0. 
Qed.
  

Lemma find_subtree_later2: forall {X: Type} (b:nat) sk k1 k2 t1 t2 
                                 (l1 l2: list(nat*bplustree b X)),
  kvl_sorted ((k1, t1) :: l1 ++ (k2, t2) :: l2) ->
  find_subtree sk ((k1, t1) :: l1 ++ (k2, t2) :: l2) = Some (k2, t2) ->
  find_subtree sk (l1 ++ (k2, t2) :: l2) = Some (k2, t2).
Proof. 
  intros. 
  destruct l1. 
  Case "l1 = []".
    destruct l2. 
	SCase "l2 = []".
	    simpl in H0. 
	    remember (ble_nat k1 sk). destruct b0. remember (blt_nat sk k2). destruct b0.
	    simpl in H0. inversion H0. subst. simpl. rewrite <- Heqb0. reflexivity.
	    simpl in H0. simpl. remember (ble_nat k2 sk). destruct b0. reflexivity. inversion H0.
	    simpl in H0. remember (ble_nat k2 sk). destruct b0. simpl. rewrite <- Heqb1. reflexivity.
	    inversion H0.
	SCase "l2 = p :: l2".
	  destruct p. simpl in H0. remember (ble_nat k1 sk). destruct b1. remember (blt_nat sk k2). destruct b1.
	  simpl in H0. inversion H0. 
	  symmetry in Heqb1. symmetry in Heqb0. apply ble_nat_true in Heqb1. apply blt_nat_true in Heqb0.
	  exfalso. omega. simpl in H0. 
	  simpl in H.
	  remember (ble_nat k2 sk). destruct b1. remember (blt_nat sk n). destruct b1. simpl in H0.
	  simpl. rewrite <- Heqb2. rewrite <- Heqb3. simpl. reflexivity. simpl.
	  rewrite <- Heqb3. rewrite <- Heqb2. simpl. apply H0.
	  simpl in H0. simpl. rewrite <- Heqb2. simpl. apply H0. simpl. simpl in H0. apply H0.
  Case "l1 = p :: l1".
    destruct p. simpl in H. 
    assert (find_subtree sk ((k1, t1) :: ((n, b0) :: l1) ++ (k2, t2) :: l2) =
            Some (k2, t2)) by assumption.
    apply find_subtree_returns_a_lesser_key in H0.
	apply list_tail_is_sorted in H.
	apply kvl_sorted_key_across_app in H. simpl in H1.
	remember (ble_nat k1 sk). destruct b1. remember (blt_nat sk n). destruct b1.
	simpl in H1. inversion H1. subst. symmetry in Heqb0. apply blt_nat_true in Heqb0. exfalso. omega.
	simpl in H1. apply H1. simpl. simpl in H1. apply H1. simpl. omega. assumption.
Qed.
	  
 

Lemma find_subtree_later3: forall {X: Type} (b:nat) sk k1 k2 t1 t2
                           (l1 l2: list(nat*bplustree b X)),
  kvl_sorted ((k1, t1) :: l1 ++ (k2, t2) :: l2) ->
  k2 <= sk ->
  find_subtree sk (l1 ++ (k2, t2) :: l2) = Some (k2, t2) ->
  find_subtree sk ((k1, t1) :: l1 ++ (k2, t2) :: l2) = Some (k2, t2).
Proof.
  intros. destruct l1.
  Case "l1 = []".
    simpl. remember (ble_nat k1 sk). destruct b0. remember (blt_nat sk k2). destruct b0.
    simpl. symmetry in Heqb1. apply blt_nat_true in Heqb1. exfalso. omega. simpl.
    simpl in H1. apply H1. simpl. apply H1.
  Case "l1 = p :: l1".
    destruct p. simpl. 
    remember (ble_nat k1 sk). destruct b1. remember (blt_nat sk n). destruct b1. simpl.
    apply list_tail_is_sorted in H. apply kvl_sorted_key_across_app in H.
    symmetry in Heqb0. apply blt_nat_true in Heqb0. exfalso. omega.
    simpl. apply H1. simpl. apply H1.
Qed.
    
  


Lemma find_subtree_key_in_middle: forall {X: Type} b sk k1 k2 t1 t2 
                                         (l1 l2: list(nat*bplustree b X)),
  kvl_sorted (l1 ++ (k1, t1) :: (k2, t2) :: l2) -> 
  (find_subtree sk (l1 ++ (k1, t1) :: (k2, t2) :: l2) = Some (k1, t1) <->
  k1 <= sk < k2).
Proof. 
  intros. split; intro.
  Case "->".
    induction l1. 
    SCase "l1 = []".
      simpl in H. simpl in H0. remember (ble_nat k1 sk && blt_nat sk k2).
      destruct b0. 
        symmetry in Heqb0. apply ble_and_blt_true in Heqb0. omega.
        unfold andb in Heqb0.
        destruct l2.
        destruct (ble_nat k2 sk). inversion H0. 
        apply kvl_sorted_key_across_app with (l1:=[])(l2:=[]) in H. omega. inversion H0.
        destruct p. destruct (ble_nat k2 sk && blt_nat sk n). inversion H0.
        apply kvl_sorted_key_across_app with (l1:=[]) (l2:=(n, b0):: l2) in H. omega.
        assert ((k1, t1) :: (k2, t2) :: (n, b0) :: l2 = (k1, t1) :: [(k2, t2)] ++ (n, b0) :: l2).
          simpl. reflexivity.
        rewrite H1 in H. 
        assert (kvl_sorted ((k1, t1) :: [(k2, t2)] ++ (n, b0) :: l2)) by assumption.
        apply kvl_sorted_key_across_app in H. 
        apply find_subtree_now_or_later in H0. omega.
        simpl in H2. do 2 apply list_tail_is_sorted in H2. assumption.
      SCase "l1 = a :: l1".
        destruct a. repeat rewrite <- app_comm_cons in H0. apply find_subtree_later2 in H0.
        apply IHl1. apply list_tail_is_sorted in H. apply H. assumption. assumption.
    Case "<-".
      induction l1.
      SCase "l1 = []".
        simpl. 
        assert (ble_nat k1 sk && blt_nat sk k2 = true). 
          unfold andb. assert (ble_nat k1 sk = true). apply ble_nat_true. omega.
          rewrite H1. apply blt_nat_true. omega.
        rewrite H1. reflexivity.
      SCase "l1 = a :: l1".
        destruct a. repeat rewrite <- app_comm_cons. eapply find_subtree_later3. assumption.
        omega. apply IHl1. apply list_tail_is_sorted in H. apply H.
Qed.
      

Lemma find_subtree_key_in_last: forall {X: Type} b sk t key 
                                      (l: list(nat*bplustree b X)), 
  kvl_sorted (l ++ [(key, t)]) -> 
  (find_subtree sk (l ++ [(key, t)]) = Some (key, t) <->
  key <= sk).
Proof.
  intros. split; intro. 
  Case "->".
    induction l. simpl in H. remember (ble_nat key sk). destruct b0; symmetry in Heqb0.
    apply ble_nat_true in Heqb0. omega. simpl in H0. rewrite Heqb0 in H0. inversion H0.
    simpl in H. destruct a. assert (kvl_sorted ((n, b0) :: l ++ [(key, t)])) by assumption.
    apply kvl_sorted_key_across_app in H. 
    destruct l.
    SCase "l = []".
      simpl in H0. destruct (ble_nat n sk && blt_nat sk key). inversion H0. omega.
      remember (ble_nat key sk). destruct b1; symmetry in Heqb1. apply ble_nat_true in Heqb1.
      omega. inversion H0.
    SCase "l = p :: l".
      destruct p. simpl in H0. destruct (ble_nat n sk && blt_nat sk n0). inversion H0. omega.
      apply IHl. apply list_tail_is_sorted in H1. assumption. apply H0.
  Case "<-".
    induction l. 
    SCase "l = []".  
      simpl. assert (ble_nat key sk = true). apply ble_nat_true. omega. rewrite H1.
      reflexivity.
    SCase "l = a :: l".
      destruct a. destruct l. apply kvl_sorted_key_across_app in H. simpl.
      assert (ble_nat n sk && blt_nat sk key = false). unfold andb.
        assert (ble_nat n sk = true). apply ble_nat_true. omega.  rewrite H1.
          apply blt_nat_false. omega.
      rewrite H1. assert (ble_nat key sk = true). apply ble_nat_true. omega.
      rewrite H2. reflexivity.
      destruct p. 
      assert (kvl_sorted (((n, b0) :: (n0, b1) :: l) ++ [(key, t)])) by assumption.
      simpl. apply kvl_sorted_key_across_app in H. 
      assert ( ble_nat n sk && blt_nat sk n0 = false). unfold andb. 
        assert (ble_nat n sk = true).
          apply ble_nat_true. omega.
        rewrite H2. apply list_tail_is_sorted in H1. apply kvl_sorted_key_across_app in H1. 
        apply blt_nat_false. omega.
      rewrite H2. apply IHl.
      apply list_tail_is_sorted in H1. apply H1.
Qed.
    

  












