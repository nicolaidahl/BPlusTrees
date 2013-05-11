Require Export InductiveDataTypes.
Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.



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

Lemma find_subtree_before_head_None: forall {X: Type} {b: nat} n k t kpl,
  n > k -> kvl_sorted ((n, t) :: kpl) ->
  @find_subtree X b k ((n, t) :: kpl) = None.
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
  

Lemma find_subtree_later: forall {X: Type} b n1 n2 k t1 t2 kpl key subtree,
  n1 > k \/ k >= n2 ->
  kvl_sorted((n1, t1) :: (n2, t2) :: kpl) ->
  @find_subtree X b k ((n1, t1) :: (n2, t2) :: kpl) = Some (key, subtree) ->
  @find_subtree X b k ((n2, t2) :: kpl) = Some (key, subtree).
Proof.
  intros. destruct H. 
  eapply find_subtree_before_head_None in H0. rewrite H0 in H1. inversion H1.
  assumption.
  simpl in H1. assert (~ (k < n2)). omega. apply blt_nat_false in H2.
  assert (ble_nat n1 k && blt_nat k n2 = false). unfold andb. rewrite H2. 
    destruct (ble_nat n1 k). reflexivity. reflexivity.
   rewrite H3 in H1. apply H1.
Qed.



Lemma find_subtree_one_impl_found: forall {X: Type} b k n t key subtree,
  k >= n ->
  @find_subtree X b k [(n, t)] = Some (key, subtree) ->
  n = key /\ t = subtree.
Proof.
  intros. simpl in H0. destruct (ble_nat n k). inversion H0. split. reflexivity. 
  reflexivity. inversion H0.
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

Lemma find_subtree_returns_a_bigger_key : forall (X: Type) (b sk key: nat) (child: bplustree b X) (l: list (nat * bplustree b X)),
  2 <= length l ->
  kvl_sorted l -> 
  find_subtree sk l = Some (key, child) ->
  key <= sk.
Proof.
  admit.
Admitted.
  (*
  intros.
  induction l.
  Case "l = []".
    inversion H.
    simpl in H3. exfalso. omega.
  Case "l = a::l". destruct a.
    simpl in H0.
    destruct l. inversion H. simpl in H3. exfalso. omega.
    SCase "l = a::p::l".
    destruct p.
    remember (blt_nat sk n0) as here.
    destruct here.
    SSCase "here".
      inversion H0. subst. clear H0.
      inversion H. clear H1. clear H2. clear H3.  clear H4. clear H5. clear H7. clear H0.
      inversion H6. clear H2. clear H0. clear H1. clear H3. clear H4. clear H5.
      clear n1. clear n2. clear x1. clear x2. clear lst.
      apply blt_nat_true in H7.
      symmetry in Heqhere. apply blt_nat_true in Heqhere.
      
      inversion Heqhere. apply ble_nat_true in H1.
      apply H1.
    SCase "later".
      destruct l.
      simpl in H0.
      symmetry in Heqhere. apply andb_false_iff in Heqhere. 
      inversion Heqhere.
      apply ble_nat_false in H1.
      assert (sk < n) by omega.
      simpl in H0. inversion H0. subst.
      inversion H.
      inversion H9.
      apply blt_nat_true in H17.
      clear H4. clear H5. clear H6. clear H7. clear H8. clear H9. clear H10. clear H3.
      clear H13. clear H11. clear H12. clear H14. clear H15. clear H16.
      clear n1. clear n2. clear x1. clear x2. clear lst. clear kpl.
      apply 
      apply IHl.
*)      

Lemma find_subtree_after_replace: forall (X: Type) (b key sk: nat) (t1 t2: bplustree b X) (kpl: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  find_subtree sk kpl = Some (key, t1) ->
  find_subtree sk (insert_into_list key t2 kpl) = Some (key, t2).
Proof.
  admit.
Admitted.
(*
  intros.
  apply find_subtree_impl_kpl_app in H0.
  do 2 destruct H0. inversion H0.
  rewrite H1.
  rewrite override_in_list_app.
  destruct H2.
  Case "t1 appeared at the end of the tree".
    subst.
    destruct witness.
    inversion H. simpl in H3. exfalso. omega.
    destruct p.
    rewrite <- app_comm_cons.
    
  
  
  
  SearchAbout [find_subtree].
  
  induction kpl.
  Case "kpl = []".
    simpl. reflexivity.
  Case "kpl = a::kpl". destruct a.
    simpl.
    destruct kpl.
    inversion H0. rewrite ble_nat_symm. rewrite <- beq_nat_refl.
    simpl. reflexivity.
    destruct p.
    
    remember (ble_nat key n) as keylen.
    destruct keylen; symmetry in Heqkeylen; [apply ble_nat_true in Heqkeylen | apply ble_nat_false in Heqkeylen].
      remember (beq_nat key n) as keyeqn.
      destruct keyeqn; symmetry in Heqkeyeqn; [apply beq_nat_true_iff in Heqkeyeqn | apply beq_nat_false_iff in Heqkeyeqn].
      subst.
      simpl in H0.
      simpl.
      remember (ble_nat n sk && blt_nat sk n0) as here.
      destruct here. reflexivity.
        remember 
*)      

Lemma find_subtree_impl_key_appears : forall (X: Type) (b k key: nat) 
                                      (kpl: list (nat * bplustree b X)) (subtree: bplustree b X), 
  find_subtree k kpl = Some (key, subtree) -> 
  appears_in_kvl key kpl.
Proof.
  intros. induction kpl. simpl in H. inversion H.
  destruct a. destruct kpl.
  Case "kpl = []".
    apply find_subtree_one_impl_found in H. destruct H. rewrite H.
    apply aik_here.
    
Admitted.















