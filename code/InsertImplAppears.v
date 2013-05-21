Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.
Require Export ValidBPlusTree.
Require Export AppearsInKVL.
Require Export AppearsInTree.
Require Export ElementAtIndexProofs.
Require Export SplitCutList.
Require Export FindSubtreeProofs.
Require Export InsertProofs.
Require Export KvAppearsInTree.
Require Export ValidSplitsProofs.


Theorem insert_leaf_impl_appears_split_right : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b <> 0 -> 
  kvl_sorted leaf -> 
  ~ (appears_in_kvl k leaf) -> 
  element_at_index (pred b) leaf = Some (kb, vb) -> 
  kb < k -> length leaf = mult b 2 -> 
  insert_leaf b k v leaf = (left, Some kvl) -> 
  kv_appears_in_kvl k v kvl.
Proof.
  intros. 
  
  destruct leaf.
  Case "leaf = []".
    intros.
    destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
    inversion H4.
  Case "leaf = a::leaf".
    intros.
    destruct p.
    remember (beq_nat n k) as neqk.
    destruct neqk; symmetry in Heqneqk; [apply beq_nat_true_iff in Heqneqk|apply beq_nat_false_iff in Heqneqk].
    SCase "n = k".
      subst. apply ex_falso_quodlibet. apply H1. apply aik_here.
    SCase "n <> k".
      remember (ble_nat n k) as nlek.
      destruct nlek; symmetry in Heqnlek; [apply ble_nat_true in Heqnlek|apply ble_nat_false in Heqnlek].
      SSCase "n <= k".
       apply le_lt_or_eq_iff in Heqnlek. inversion Heqnlek. clear Heqnlek.
       SSSCase "n < k".
         rewrite insert_leaf_cons_gt_overflow in H5; try assumption; try omega.
         remember (split_list b ((n, x) :: insert_into_list k v leaf)) as split.
         destruct split. inversion H5. subst. clear H5.
         symmetry in Heqsplit. 
         assert (split_list b ((n, x) :: insert_into_list k v leaf) = (left, kvl)) by assumption. 
         apply split_list_preserves_lists in Heqsplit.
         assert ((n, x) :: insert_into_list k v leaf = left ++ kvl) by assumption.
         
         apply kv_appears_in_kvl_dist_app with (k := k) (v := v) in Heqsplit.
         inversion Heqsplit. clear Heqsplit. 
         SSSSCase "appears_in_kvl n left".
           (* This case is bogus, needs an inversion *)
           apply split_list_left_length in H5.
           simpl in H4. 
                      
           apply element_unchanged_by_inserting_greater_key with (k3 := k) (v3 := v) in H2; try assumption.
           
           apply element_at_index_pred_b_implies_left_below_S_b with (l1 := left) (l2 := kvl) in H2; try assumption.
           apply key_greater_than_all_keys_does_not_appear_ble with (k:=k) in H2; try assumption.
           (* We've found our inversion - k both appears and does not appear in left *)
           apply ex_falso_quodlibet. apply H2. apply kv_appears_in_kvl_impl_appears_in_kvl in H8. assumption.
           
            
           (* Now we just need to prove all of the assumptions *)            
           symmetry in H7. apply split_preserves_sort in H7; try assumption.
           inversion H7. assumption.
           
           apply insert_preserves_sort_cons; assumption. 
           apply insert_preserves_sort_cons; assumption.
           apply sort_ignores_value with (v1 := x) (v2 := vb); assumption.
           simpl in H4.
           rewrite <- insert_new_into_list_increases_length with (k := k) (v := v) (l := leaf) in H4.
           simpl. rewrite H4.  omega.
           apply list_tail_is_sorted in H0. assumption.
           unfold not. intro. apply H1. apply aik_later. assumption.
           reflexivity.
         SSSSCase "appears_in_kvl n kvl".
           assumption.
         apply kv_aik_later.
         apply insert_into_list_appears.
         unfold not. intro. apply H1. apply aik_later. assumption.
       SSSCase "n = k".
         apply ex_falso_quodlibet. apply Heqneqk. apply H6.
      SSCase "n > k".
        rewrite insert_leaf_cons_lt_overflow in H5; try assumption; try omega.
        
        apply element_at_index_impl_appears in H2.
        apply appears_in_kvl_app in H2.
        do 3 destruct H2.
        inversion H0. subst. simpl in H4. 
        assert (~(1 = b*2)). omega.
        apply ex_falso_quodlibet. apply H6. apply H4.
        
        subst.
        apply blt_nat_true in H10.
        
        rewrite H2 in H0.
        destruct witness.
        simpl in *.
        assert (n > kb) by omega.
        assert (n > k) by omega.
        
        inversion H2. rewrite H11 in H6. apply n_lt_n_inversion with (n := kb). apply H6.
        rewrite <- app_comm_cons in H2.
        inversion H2. rewrite <- H7 in H0.
        apply kvl_sorted_key_across_app in H0.
        apply ex_falso_quodlibet.
        omega.
Qed.



Theorem insert_leaf_impl_appears_split_left : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index (pred b) leaf = Some (kb, vb) -> 
  k < kb -> length leaf = mult b 2 ->
  insert_leaf b k v leaf = (left, Some kvl) -> kv_appears_in_kvl k v left.
Proof.
  intros.
  destruct leaf.
  Case "leaf = []".
    intros.
    destruct b. apply ex_falso_quodlibet. apply H. reflexivity. 
    simpl in H4. inversion H4.
  Case "leaf = a::leaf".
    intros.
    destruct p.
    remember (beq_nat n k) as neqk.
    destruct neqk; symmetry in Heqneqk; [apply beq_nat_true_iff in Heqneqk|apply beq_nat_false_iff in Heqneqk].
    
    SCase "n = k".    
      rewrite insert_leaf_cons_eq in H5;
      inversion H5.
      assumption.
      assumption.
      omega. 
      simpl in H4. simpl. omega.
    SCase "n <> k".
      remember (ble_nat n k) as nlek.
      destruct nlek; symmetry in Heqnlek; [apply ble_nat_true in Heqnlek|apply ble_nat_false in Heqnlek].
      SSCase "n <= k".
       apply le_lt_or_eq_iff in Heqnlek. inversion Heqnlek.
       SSSCase "n < k".
         rewrite insert_leaf_cons_gt_overflow in H5; try assumption.
         remember (split_list b ((n, x) :: insert_into_list k v leaf)) as split. 
         destruct split.
         assert ((l, l0) = split_list b ((n, x) :: insert_into_list k v leaf)) by assumption.
         symmetry in Heqsplit.
         apply split_list_preserves_lists in Heqsplit. inversion H5. subst.
         destruct left. 
         SSSSCase "left = []".
           symmetry in H7.
           apply split_list_left_length in H7.
           simpl in H7. rewrite <- H7 in H.
           apply ex_falso_quodlibet. omega.
           simpl in H4.
           rewrite <- insert_new_into_list_increases_length with (k:=k) (v:=v) (l := leaf) in H4.
           simpl.
           rewrite H4. omega.
           apply list_tail_is_sorted in H0. apply H0. 
           unfold not. intro. apply H1.
           apply aik_later. apply H8.
           reflexivity.
         SSSSCase "left = p::left". 
           destruct p.
           rewrite <- app_comm_cons in Heqsplit. inversion Heqsplit.
           apply kv_appears_in_kvl_dist_app with (k := k) (v := v) in H11.
           destruct H11.
           SSSSSCase "appears in left".
             apply kv_aik_later. apply H8.
           SSSSSCase "appears in right".
             (* This case is bogus *)
             symmetry in H7. apply split_list_left_length in H7. 
             rewrite <- H9 in H7. rewrite <- H10 in H7.
             
             apply element_changed_by_inserting_smaller_key with (k3:=k) (v3:= v) (b:= pred b) in H2.
             replace (S (pred b)) with (b) in H2 by omega.
             simpl in H2.
             remember (ble_nat k n) as klen'.
             destruct klen'; symmetry in Heqklen'; [apply ble_nat_true in Heqklen'|apply ble_nat_false in Heqklen'].
             apply ex_falso_quodlibet. omega.              
             
             apply element_at_index_b_implies_right_above_b with (l1 := ((n0,x0)::left)) (l2 := kvl) in H2.
             apply key_smaller_than_all_keys_does_not_appear with (k:= k) in H2.
             
             apply ex_falso_quodlibet. apply H2. apply kv_appears_in_kvl_impl_appears_in_kvl in H8. assumption.
             symmetry in Heqsplit. 
             assert (kvl_sorted ((n, x) :: insert_into_list k v leaf)).
               apply insert_preserves_sort_cons.
               omega. apply H0.
             apply split_preserves_sort with (l1 := ((n0,x0)::left)) (l2 := kvl) in H11.
             inversion H11. assumption.
             assumption. omega.
             
             apply insert_preserves_sort_cons.
             omega. apply H0.
             assumption.
             simpl in H7. simpl. omega.
             
             apply sort_ignores_value with (v1:=x)(v2:=vb) in H0. apply H1. apply H0.
             omega.
             
             simpl in H4.
             rewrite <- insert_new_into_list_increases_length with (k:=k) (v:=v) (l := leaf) in H4.
             simpl. rewrite H4. omega.
             apply list_tail_is_sorted in H0. assumption.
             unfold not. intro. apply H1. apply aik_later. assumption.
             reflexivity.
           apply insert_into_list_appears.
           unfold not. intro. apply H1. apply aik_later. assumption.           
        SSSCase "n = k".
         apply ex_falso_quodlibet. apply Heqneqk. apply H6.
      SSCase "n > k".
        rewrite insert_leaf_cons_lt_overflow in H5; try assumption.
        remember (split_list b ((k, v) :: (n, x) :: leaf)) as split. 
        destruct split.
          symmetry in Heqsplit.
          assert (split_list b ((k, v) :: (n, x) :: leaf) = (l, l0)) by assumption.
          apply split_list_preserves_lists in Heqsplit; try assumption. inversion H5. subst.
          destruct left. 
            SSSCase "left = []".
              apply split_list_left_length in H6.
              simpl in H6. rewrite <- H6 in H.
              apply ex_falso_quodlibet. omega.
              simpl in H4.
              simpl.
              rewrite H4.
              omega.
            SSSCase "left = p::left".
              destruct p.
              rewrite <- app_comm_cons in Heqsplit. inversion Heqsplit. apply kv_aik_here.
              omega.
Qed.


Theorem insert_leaf_impl_appears_normal : forall {X: Type} {b: nat} (leaf left: list (nat * X)) (k: nat) (v: X),
  b <> 0 -> kvl_sorted leaf -> 
  ~ (appears_in_kvl k leaf) -> 
  length leaf < mult b 2 ->
  insert_leaf b k v leaf = (left, None) -> 
  kv_appears_in_kvl k v left.
Proof.
  intros. 
  
  destruct leaf.
  Case "leaf = []".
    intros.
    destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
    compute in H3. inversion H3. apply kv_aik_here.
  Case "leaf = a::leaf".
    intros.
    destruct p.
    remember (beq_nat n k) as neqk.
    destruct neqk; symmetry in Heqneqk; [apply beq_nat_true_iff in Heqneqk|apply beq_nat_false_iff in Heqneqk].
    SCase "n = k".
      rewrite insert_leaf_cons_eq in H3.
      inversion H3. apply kv_aik_here. apply H. apply H0. 
      rewrite Heqneqk. reflexivity.
      simpl. simpl in H2. omega.
    SCase "n <> k".
      remember (ble_nat n k) as nlek.
      destruct nlek; symmetry in Heqnlek; [apply ble_nat_true in Heqnlek|apply ble_nat_false in Heqnlek].
      SSCase "n <= k".
       apply le_lt_or_eq_iff in Heqnlek. inversion Heqnlek.
       SSSCase "n < k".
         rewrite insert_leaf_cons_gt in H3.
         inversion H3. apply kv_aik_later.
         apply insert_into_list_appears.
         apply H.
         apply H0.
         omega.
         simpl in H2. simpl. omega. 
       SSSCase "n = k".
         apply ex_falso_quodlibet. apply Heqneqk. apply H4.
      SSCase "n > k".
        rewrite insert_leaf_cons_lt in H3.
        inversion H3. apply kv_aik_here.
        apply H.
        apply H0.
        omega.
        simpl in H2. simpl. omega.
Qed.

Theorem insert_leaf_impl_appears : forall {X: Type} {b: nat} (k: nat) (v: X) (leaf left: list (nat * X)) (rightOption: option (list (nat * X))),
  b <> 0 -> kvl_sorted leaf ->
  ~ (appears_in_kvl k leaf) -> 
  length leaf <= mult b 2 ->
  insert_leaf b k v leaf = (left, rightOption) ->
  kv_appears_in_kvl k v left \/ 
  (exists right, rightOption = Some(right) /\ kv_appears_in_kvl k v right).
Proof.
  intros.
  remember (blt_nat (length leaf) (b * 2)) as blt_length_b.
  destruct blt_length_b; symmetry in Heqblt_length_b; [apply blt_nat_true in Heqblt_length_b | apply blt_nat_false in Heqblt_length_b].
  Case "less".
    left.
    destruct rightOption.
    SCase "rightOption = Some".
      unfold insert_leaf in H3.
      remember (ble_nat (length (insert_into_list k v leaf)) (b * 2)) as tl.
      destruct tl.
      inversion H3.
      symmetry in Heqtl. apply ble_nat_false in Heqtl.
      apply ex_falso_quodlibet. apply Heqtl.
      apply insert_new_into_list_increases_length_lt with (k := k) (v := v) in Heqblt_length_b; try assumption.
    SCase "rightOption = None".  
      eapply insert_leaf_impl_appears_normal. 
        apply H.
        apply H0.
        apply H1.
        apply Heqblt_length_b.
        apply H3.
  Case "equal".
    assert (length leaf = b * 2) by omega.
    assert (b <= length leaf) by omega.
    remember (pred b).
    assert (n < length leaf) by omega.
    assert (leaf <> []).
      destruct leaf. simpl in H6. apply ex_falso_quodlibet. omega.
      unfold not. intro. inversion H7.
    destruct rightOption.
    SCase "rightOption = Some".
      apply list_of_length_b_implies_element_at_b with (b := n) (kvl := leaf) in H7; try assumption.
      rewrite Heqn in H7. clear Heqn. clear H6. clear n.
      destruct H7. destruct H6.
      remember (ble_nat witness k) as ble_kb_k.
      destruct ble_kb_k; symmetry in Heqble_kb_k; [apply ble_nat_true in Heqble_kb_k | apply ble_nat_false in Heqble_kb_k].
        apply le_lt_or_eq_iff in Heqble_kb_k.
        inversion Heqble_kb_k.
        SSCase "right".
          right. exists l.
          split.
          SSSCase "right = right".
            reflexivity.
          SSSCase "appears in".
            eapply insert_leaf_impl_appears_split_right.
              apply H.
              apply H0.
              apply H1.
              apply H6.
              apply H7.
              apply H4.
              apply H3.
        SSCase "equals".
          rewrite H7 in H6.
          apply element_at_index_impl_appears in H6.
          apply ex_falso_quodlibet. apply H1. apply H6.   
      SSCase "split left".
        left.
        eapply insert_leaf_impl_appears_split_left.
          apply H.
          apply H0.
          apply H1.
          apply H6.
          omega.
          apply H4.
          apply H3.
    SCase "rightOption = None".
        unfold insert_leaf in H3.
        remember (ble_nat (length (insert_into_list k v leaf)) (b * 2)) as tl.
        destruct tl.
        symmetry in Heqtl. apply ble_nat_true in Heqtl.
        apply insert_new_into_list_increases_length with (k:=k) (v:=v) in H4; try assumption.
        rewrite H4 in Heqtl.
        apply ex_falso_quodlibet. omega.
        inversion H3.
Qed.

Lemma insert_leaf_preserves_sort: forall (X: Type) b k (v:X) l l1 l2,
  kvl_sorted l ->
  insert_leaf b k v l = (l1, Some l2) ->
  kvl_sorted(l1 ++ l2).
Proof.
  intros.
  unfold insert_leaf in H0.
  remember (ble_nat (length (insert_into_list k v l)) (b * 2)).
  destruct b0.
  inversion H0.
  remember (split_list b (insert_into_list k v l)). destruct p.
  symmetry in Heqp. apply split_list_preserves_lists in Heqp.
  inversion H0. subst.
  assert (kvl_sorted (insert_into_list k v l)).
    apply insert_preserves_sort. apply H.
  rewrite Heqp in H1. apply H1.
Qed.


Lemma split_list_move_first: forall (X: Type) b k1 v1 (l l1 l2: list (nat * X)),
  b <> 0 -> length l > 1 ->
  (l1, l2) = split_list (S b) ((k1, v1) :: l) ->
  exists l3, ((k1, v1) :: l3, l2) = split_list b l.
Proof.
  intros X b.
  induction b; intros.
    exfalso. omega.
  Case "b = S b".
    destruct l.
      SCase "l = []".
        simpl in H0. exfalso. omega.
      SCase "l = p :: l".
        unfold split_list in H1. simpl in H1.
  
  
  induction l; intros.
  (*Case "l = []".
    simpl in H0. exfalso. omega.
  Case "l = a :: l1".
    destruct a.
    
    unfold split_list in H1. simpl in H1.
    assert (split_list (S b) ((k1, v1) :: (n, x) :: l) = ((k1, v1) :: cut_list_left b ((n, x) :: l), cut_list_right b ((n, x) :: l))).
      unfold split_list. simpl. reflexivity.
    unfold split_list in H2. simpl in H2.*)
Admitted.




Lemma insert'_overflow_impl_lesser_than_next: forall (X: Type) (b k k1 k2 k3: nat) (v: X) (t1 t1' t2 t3: bplustree b X) (l1 l2: list (nat * bplustree b X)),
  valid_bplustree b X t1 ->
  kvl_sorted (l1++(k1,t1)::(k3,t3)::l2) ->
  valid_splits b X (l1++(k1,t1)::(k3,t3)::l2) ->
  find_subtree k (l1++(k1,t1)::(k3,t3)::l2) = Some(k1, t1) ->
  insert' (height t1) k v t1 = (t1', Some(k2, t2)) ->

  k2 < k3.
Proof.
  intros.
  apply valid_splits_elim_middle in H1.
  assert (k1 <= k).
    apply find_subtree_returns_a_lesser_key in H2. omega.
    rewrite app_length. simpl. omega. apply H0.
  assert (k < k3).
    apply find_subtree_impl_kpl_app in H2. do 2 destruct H2.
    inversion H2.
    apply kvl_sorted_elim_common_head in H5.
    inversion H6; rewrite <- H5 in H7. inversion H7.
    do 3 destruct H7. inversion H7. inversion H8.
    omega.
    apply H0. rewrite H5 in H0. apply H0.
  assert (k1 <= k < k3) by omega.

  destruct t1. 
  Case "t1 is a leaf".
    simpl in H3.
    remember (insert_leaf b k v l) as il.
    destruct il. destruct o.
    unfold insert_leaf in Heqil.
    remember (ble_nat (length (insert_into_list k v l)) (b * 2)) as fits_here.
    destruct fits_here. inversion Heqil.
    remember (split_list b (insert_into_list k v l)) as sl.
    destruct sl as [left right]. inversion Heqil.
    rewrite H8 in *. rewrite H9 in *. clear H8. clear H9. clear Heqil.
    assert (right <> []).
      assert (length (insert_into_list k v l) > b).
        symmetry in Heqfits_here. apply ble_nat_false in Heqfits_here.
        omega.
      apply cut_right_not_nil in H7.
      unfold split_list in Heqsl.
      inversion Heqsl. assumption.
    destruct right. exfalso. apply H7. reflexivity. 
    destruct p.
    inversion H3. rewrite H10 in *. clear H9. clear H10. clear H11.
    clear H3.
    admit.
    inversion H3.
    admit.
Admitted.

Lemma insert'_impl_appears_normal : forall (X: Type) (b k n: nat) (v: X) (t1 t2: bplustree b X) (kpl: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  kv_appears_in_tree k v t2 ->
  find_subtree k kpl = Some (n, t1) ->
  ~ appears_in_tree k t1 ->

  kv_appears_in_tree k v (bptNode b X (insert_into_list n t2 kpl)).
Proof.
  intros. 
  remember (insert_into_list n t2 kpl) as kpl'.
  assert (find_subtree k kpl' = Some (n, t2)).
    rewrite Heqkpl'.
    inversion H.
    apply find_subtree_after_replace with (t1 := t1); assumption.
  assert (length kpl = length kpl').
    rewrite Heqkpl'.
    inversion H.
    apply find_subtree_impl_key_appears in H1.
    apply override_in_list_preserves_length; try assumption.
  assert (2 <= length kpl').
    inversion H.
    omega.
  assert (kvl_sorted kpl').
    rewrite Heqkpl'.
    inversion H.
    apply insert_preserves_sort; assumption.
  apply kv_appears_in_tree_when_appears_in_subtree_and_found with (kpl := kpl') (subtree := t2) (key := n); try reflexivity; try assumption. 
Qed.

Lemma insert'_impl_appears_overflow_left: forall (X: Type) (b k k1 k2 ok: nat) (v: X) (t1 t1' t2 ot0: bplustree b X) (kpl kpl' left right: list (nat* bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  insert' (height t1) k v t1 = (t1', Some (k2, t2)) ->
  find_subtree k kpl = Some (k1, t1)->
  kpl' = insert_into_list k1 t1' (insert_into_list k2 t2 kpl) ->
  length kpl' > b * 2 + 1 ->
  (ok, ot0) :: right = cut_list_right (b + 1) kpl' ->
  left = cut_list_left (b + 1) kpl' ->
  k < k2 ->
  kv_appears_in_tree k v t1' ->

  k < ok /\
   kv_appears_in_tree k v (bptNode b X left) \/
   ok <= k /\ kv_appears_in_tree k v (bptNode b X ((0, ot0) :: right)).
Proof.
  intros.
  assert (find_subtree k kpl = Some (k1, t1)) by assumption.
  apply find_subtree_impl_kpl_app in H8.
  do 2 destruct H8. inversion H8; clear H8.
  assert (k1 <= k).
    inversion H.
    assert (1 <= length kpl) by omega.
    apply find_subtree_returns_a_lesser_key in H1; assumption.
  assert (k1 < k2).
    inversion H.
    eapply insert'_overflow_impl_greater_key with (X := X).
      apply H12.
      apply H.
      apply H1.
      apply H0.
      assumption.
  assert (length kpl' > b + 1) by omega.
  assert (kvl_sorted(kpl)) by (inversion H; assumption).
  assert (kvl_sorted(kpl')).
    subst. repeat apply insert_preserves_sort. assumption.
  assert (kvl_sorted(cut_list_right (b+1) kpl')).
    rewrite cut_list_left_right_preserves_list with (b := b+1) in H14.
    apply kvl_sorted_app in H14. inversion H14.
    assumption.
  assert (kvl_sorted(cut_list_left (b+1) kpl')).
    rewrite cut_list_left_right_preserves_list with (b := b+1) in H14.
    apply kvl_sorted_app in H14. inversion H14.
    assumption.  
  destruct witness0.
  Case "subtree was in the end of the kpl".
    right. clear H10.
    rewrite H9 in H2.
    rewrite insert_into_list_last_twice with (l:= witness) in H2; try (subst; assumption).
    assert (length kpl' = S (length kpl)).
      subst. repeat rewrite app_length. simpl.
      rewrite <- plus_Sn_m. rewrite plus_comm with (m := 1).
      simpl. rewrite plus_comm. reflexivity.
    assert (length kpl' = (S b) * 2).
      inversion H.
      omega.
    assert (length witness >= b + 1 ).
      rewrite H2 in H17.
      rewrite app_length in H17.
      simpl in H17.
      inversion H.
      omega.
    apply cut_list_right_app with (l2 :=  [(k1, t1'), (k2, t2)]) in H18.
    destruct H18. rewrite <- H2 in H18.
    rewrite H18 in H4.
    destruct witness0.
    SCase "witness0 = []".
      simpl in H4. inversion H4.
      split. assumption.
      apply kv_ait_node_here. assumption.
      omega.
    SCase "witness0 = p::witness0".
      destruct p.
      rewrite <- app_comm_cons in H4.
      inversion H4.
      assert (n <= k).
        rewrite H18 in H15. simpl in H15.
        apply kvl_sorted_key_across_app in H15.
        omega.
      split. assumption.
      apply kv_appears_in_tree_when_appears_in_subtree with (l1 := (0, b0) :: witness0) (l2 := []).
        assumption.
        omega.
        rewrite H18 in H15. simpl in H15. simpl.
        apply kvl_sorted_after_replace_head_with_zero in H15.
        assumption.
   Case "subtree was in the middle of the kpl".
     destruct p as [k3 t3].
     assert (k2 < k3). 
      eapply insert'_overflow_impl_lesser_than_next in H0.
        apply H0.
        rewrite H9 in H1. apply H1.
        rewrite H9 in H13. apply H13.
      assert (k1 < k2 < k3) by omega.
    rewrite H9 in H2.
    rewrite insert_into_list_middle_twice in H2; try (subst; assumption).
    remember (blt_nat (length witness) (b + 1)) as in_left.
    destruct in_left; symmetry in Heqin_left; [apply blt_nat_true in Heqin_left | apply blt_nat_false in Heqin_left].
    SCase "subtree fit in regular node".
      left.
      remember (beq_nat (length witness) b) as eqb.
      destruct eqb; symmetry in Heqeqb; [apply beq_nat_true_iff in Heqeqb | apply beq_nat_false_iff in Heqeqb ].
      SSCase "subtree is the right-most node".
        assert (k < ok).
          rewrite H2 in H4.
          rewrite cut_list_right_elim with (b2 := b+1) (b1 := b) (l1 := witness) in H4; try assumption.
          replace (b + 1 - b) with (1) in H4 by omega. simpl in H4.
          inversion H4.
          omega.
          omega.
          simpl. rewrite H2 in H3. rewrite app_length in H3. simpl in H3. omega.
        split. assumption.
        rewrite H2 in H5.
        rewrite H2 in H16.
        rewrite H2 in H3. rewrite app_length in H3. simpl in H3.
        rewrite cut_list_left_elim with (b2 := b+1) (b1 := b) (l1 := witness) in *; simpl; try assumption; try omega.
        replace (b + 1 - b) with (1) in * by omega.
        simpl. simpl in H16.
        destruct witness.
          simpl in Heqeqb. inversion H. exfalso. omega.
        destruct p.
        rewrite H5.
        apply kv_appears_in_tree_when_appears_in_last_subtree with (k := k) (v := v); try assumption.
      SSCase "subtree is not the right-most node".
        assert (length (witness ++ [(k1, t1'), (k2, t2)]) <= b+1).
          rewrite app_length. simpl. omega.
        apply cut_list_left_app with (b := b+1) (l2 := (k3, t3) :: witness0) in H19.
        destruct H19. rewrite app_assoc_reverse in H19. simpl in H19. 
        rewrite <- H2 in H19.
        rewrite H19 in H5.
        rewrite H5.
        rewrite app_assoc_reverse.
        assert (k < ok).
          rewrite cut_list_left_right_preserves_list with (b := b +1) in H14.
          rewrite <- H4 in H14.
          rewrite H19 in H14.
          repeat rewrite <- app_assoc in H14.
          apply kvl_sorted_app in H14. inversion H14.
          simpl in H21.
          apply list_tail_is_sorted in H21.
          apply kvl_sorted_key_across_app in H21.
          omega.
        split. assumption.
        simpl.
        eapply kv_appears_in_tree_when_appears_in_subtree; try (subst; assumption).
          omega.
          rewrite H19 in H16. rewrite app_assoc_reverse in H16. simpl in H16. apply H16.
    SCase "subtree falls in the overflow node".
      right.
      assert (length witness >= b + 1) by omega. clear Heqin_left.
      apply cut_list_right_app with (l2 := (k1, t1') :: (k2, t2) :: (k3, t3) :: witness0) in H19.
      destruct H19.
      rewrite <- H2 in H19.
      rewrite H19 in *.
      destruct witness1.
      SSCase "witness1 = []".
        simpl in H4. inversion H4.
        split. assumption.
        apply kv_ait_node_here. assumption.
        omega.
      SSCase "witness1 = p::witness1".
      destruct p. rewrite <- app_comm_cons in H4.
      inversion H4.
      assert (n <= k).
        repeat rewrite <- app_comm_cons in H15.
        apply kvl_sorted_key_across_app in H15.
        omega.
      split. assumption.
      assert (k1 <= k < k2) by omega.
      eapply kv_appears_in_tree_when_appears_in_subtree with (l1 := (0, b0)::witness1); try (subst; assumption).
        simpl in H15. simpl.
        apply kvl_sorted_after_replace_head_with_zero in H15.
        assumption.
Qed.
  
 
  

  
Lemma insert'_impl_appears_overflow_right: forall (X: Type) (b k k1 k2 ok: nat) (v: X) (t1 t1' t2 ot0: bplustree b X) (kpl kpl' left right: list (nat* bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  insert' (height t1) k v t1 = (t1', Some (k2, t2)) ->
  find_subtree k kpl = Some (k1, t1)->
  kpl' = insert_into_list k1 t1' (insert_into_list k2 t2 kpl) ->
  length kpl' > b * 2 + 1 ->
  (ok, ot0) :: right = cut_list_right (b + 1) kpl' ->
  left = cut_list_left (b + 1) kpl' ->
  k2 <= k ->
  kv_appears_in_tree k v t2 ->

  k < ok /\
   kv_appears_in_tree k v (bptNode b X left) \/
   ok <= k /\ kv_appears_in_tree k v (bptNode b X ((0, ot0) :: right)).
Proof.
  intros.
  assert (find_subtree k kpl = Some (k1, t1)) by assumption.
  apply find_subtree_impl_kpl_app in H8.
  do 2 destruct H8. inversion H8; clear H8.
  assert (k1 <= k).
    inversion H.
    assert (1 <= length kpl) by omega.
    apply find_subtree_returns_a_lesser_key in H1; assumption.
  assert (k1 < k2).
    inversion H.
    eapply insert'_overflow_impl_greater_key.
      apply H12.
      apply H.
      apply H1.
      apply H0.
      assumption.
  assert (length kpl' > b + 1) by omega.
  assert (kvl_sorted(kpl)) by (inversion H; assumption).
  assert (kvl_sorted(kpl')).
    subst. repeat apply insert_preserves_sort. assumption.
  assert (kvl_sorted(cut_list_right (b+1) kpl')).
    rewrite cut_list_left_right_preserves_list with (b := b+1) in H14.
    apply kvl_sorted_app in H14. inversion H14.
    assumption.
  assert (kvl_sorted(cut_list_left (b+1) kpl')).
    rewrite cut_list_left_right_preserves_list with (b := b+1) in H14.
    apply kvl_sorted_app in H14. inversion H14.
    assumption. 
  destruct witness0.
  Case "subtree was in the end of the kpl".
    right. clear H10.
    rewrite H9 in H2.
    rewrite insert_into_list_last_twice with (l:= witness) in H2; try (subst; assumption).
    assert (length kpl' = S (length kpl)).
      subst. repeat rewrite app_length. simpl.
      rewrite <- plus_Sn_m. rewrite plus_comm with (m := 1).
      simpl. rewrite plus_comm. reflexivity.
    assert (length kpl' = (S b) * 2).
      inversion H.
      omega.
    assert (length witness >= b + 1 ).
      rewrite H2 in H17.
      rewrite app_length in H17.
      simpl in H17.
      inversion H.
      omega.
    apply cut_list_right_app with (l2 :=  [(k1, t1'), (k2, t2)]) in H18.
    destruct H18. rewrite <- H2 in H18.
    rewrite H18 in H4.
    destruct witness0.
    SCase "witness0 = []".
      simpl in H4. inversion H4.
      split. assumption.
      apply kv_ait_node_last. assumption.
      omega. 
    SCase "witness0 = p::witness0".
      destruct p.
      rewrite <- app_comm_cons in H4.
      inversion H4.
      assert (n <= k).
        rewrite H18 in H15. simpl in H15.
        apply kvl_sorted_key_across_app in H15.
        omega.
      split. assumption.
      replace ([(k1, t1'), (k2, t2)]) with ([(k1,t1')]++[(k2, t2)]) by reflexivity.
      rewrite app_assoc.
      apply kv_appears_in_tree_when_appears_in_last_subtree with (l1 := witness0 ++ [(k1, t1')]).
        assumption.
        omega.
        rewrite H18 in H15. simpl in H15. rewrite <- app_assoc. simpl.
          apply kvl_sorted_after_replace_head_with_zero in H15.
          assumption.
  Case "subtree was in the middle of the kpl".
     destruct p as [k3 t3].
     assert (k2 < k3). 
      eapply insert'_overflow_impl_lesser_than_next in H0.
        apply H0.
        rewrite H9 in H1. apply H1.
        rewrite H9 in H13. apply H13.
      assert (k1 < k2 < k3) by omega.
    rewrite H9 in H2.
    rewrite insert_into_list_middle_twice in H2; try (subst; assumption).
    remember (blt_nat (length witness) (b)) as in_left.
    destruct in_left; symmetry in Heqin_left; [apply blt_nat_true in Heqin_left | apply blt_nat_false in Heqin_left].
    SCase "subtree fit in regular node".
      left.
      remember (beq_nat (length witness) (b-1)) as eqb.
      destruct eqb; symmetry in Heqeqb; [apply beq_nat_true_iff in Heqeqb | apply beq_nat_false_iff in Heqeqb ].
      SSCase "subtree is the right-most node".
        assert (k < ok).
          rewrite H2 in H4.
          rewrite cut_list_right_elim with (b2 := b+1) (b1 := b-1) (l1 := witness) in H4; try assumption.
          replace (b + 1 - (b - 1)) with (2) in H4 by (inversion H; omega). simpl in H4.
          inversion H4.
          inversion H10. inversion H19.
          do 3 destruct H19. inversion H19.
          inversion H23. apply H24.
          omega.
          simpl. rewrite H2 in H3. rewrite app_length in H3. simpl in H3. omega.
        split. assumption.
        rewrite H2 in H5.
        rewrite H2 in H16.
        rewrite H2 in H3. rewrite app_length in H3. simpl in H3.
        rewrite cut_list_left_elim with (b2 := b+1) (b1 := b-1) (l1 := witness) in *; simpl; try assumption; try omega.
        replace (b + 1 - (b - 1)) with (2) in * by omega.
        simpl in H5. simpl in H16.
        rewrite H5.
        destruct witness.
          simpl. apply kv_ait_node_last. assumption. omega.
        destruct p.
        simpl.
        replace ([(k1, t1'), (k2, t2)]) with ([(k1,t1')]++[(k2, t2)]) by reflexivity.
        rewrite app_assoc.
        apply kv_appears_in_tree_when_appears_in_last_subtree with (k := k) (v := v); try assumption.
          rewrite <- app_assoc. simpl. simpl in H16.
            apply H16.
      SSCase "subtree is not the right-most node".
        assert (length (witness ++ [(k1, t1'), (k2, t2), (k3, t3)]) <= b+1).
          rewrite app_length. simpl. omega.
        apply cut_list_left_app with (b := b+1) (l2 := witness0) in H19.
        destruct H19. rewrite app_assoc_reverse in H19. simpl in H19. 
        rewrite <- H2 in H19.
        rewrite H19 in H5.
        rewrite H5.
        rewrite app_assoc_reverse.
        assert (k < k3).
          inversion H10. inversion H20.
          do 3 destruct H20. inversion H20.
          inversion H21.
          assumption.
        assert (k2 <= k < k3) by omega.
        assert (k < ok).
          assert (length (witness ++ [(k1, t1'), (k2, t2)]) <= b+1).
            rewrite app_length. simpl. omega.
          eapply cut_list_right_above with (k:=k3) (v:=t3) (l2 := witness0) (l3 := (ok, ot0) :: right) in H22.
          inversion H22.
          unfold above in H27. apply ble_nat_true in H27.
          omega.
          rewrite <- app_assoc.  simpl. rewrite <- H2. assumption.
          symmetry. rewrite <- app_assoc. simpl. rewrite <- H2. assumption.
        split. assumption.  
        simpl.
        remember (witness++[(k1,t1')]) as witness'.
        replace (witness ++ (k1, t1') :: (k2, t2) :: (k3, t3) :: witness1) with (witness' ++ (k2, t2) :: (k3, t3) :: witness1).
        eapply kv_appears_in_tree_when_appears_in_subtree; try (subst; assumption).
          rewrite Heqwitness'. rewrite <- app_assoc. simpl. rewrite H19 in H16.
            rewrite <- app_assoc in H16. simpl in H16. apply H16.
          rewrite Heqwitness'. rewrite <- app_assoc. simpl. reflexivity.
    SCase "subtree falls in the overflow node".
      right.
      assert (length (witness++[(k1, t1')]) >= b+1).
        rewrite app_length. simpl. omega.
      clear Heqin_left.
      apply cut_list_right_app with (l2 := (k2, t2) :: (k3, t3) :: witness0) in H19.
      destruct H19.
      rewrite <- app_assoc in H19. simpl in H19.
      rewrite <- H2 in H19.
      rewrite H19 in *.
      assert (k < k3).
        inversion H10. inversion H20.
        do 3 destruct H20. inversion H20.
        inversion H21.
        assumption.
      destruct witness1.
      SSCase "witness1 = []".
        simpl in H4. inversion H4.
        split. assumption.
        apply kv_ait_node_here. assumption.
        omega.
      SSCase "witness1 = p::witness1".
      destruct p. rewrite <- app_comm_cons in H4.
      inversion H4.
      assert (n <= k).
        repeat rewrite <- app_comm_cons in H15.
        apply kvl_sorted_key_across_app in H15.
        omega.
      split. assumption.
      assert (k2 <= k < k3) by omega.
      eapply kv_appears_in_tree_when_appears_in_subtree with (l1 := (0, b0)::witness1); try (subst; assumption).
        simpl in H15. simpl.
        apply kvl_sorted_after_replace_head_with_zero in H15.
        assumption.
Qed.
  
Lemma insert'_leaf_disregards_counter: forall (X: Type) (b counter k: nat) (v: X) (kvl: list (nat * X)),
  insert' counter k v (bptLeaf b X kvl) = let (fst, snd_opt) := insert_leaf b k v kvl in
    match snd_opt with
      | Some snd =>
         match 
           match snd with
             | nil => None
             | (k0, _) :: _ => Some k0
           end
         with
           | Some first_key =>(bptLeaf b X fst, Some (first_key, bptLeaf b X snd))
           | None => (bptLeaf b X fst, None)
         end
      | None => (bptLeaf b X fst, None)
    end.
Proof.
  intros.
  unfold insert'.
  destruct counter.
  reflexivity.
  reflexivity.
Qed.


Theorem insert'_impl_appears : forall {X: Type} (counter b k: nat) (v: X) (kpl: list (nat * bplustree b X)) (left: bplustree b X) (rightOption: option (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  not (appears_in_tree k (bptNode b X kpl)) -> 
  counter = (height (bptNode b X kpl)) ->
  insert' counter k v (bptNode b X kpl) = (left, rightOption) ->
  
  (rightOption = None /\ kv_appears_in_tree k v left)
    \/
  (exists split, exists right, rightOption = Some(split, right)
      /\ ((k < split /\ kv_appears_in_tree k v left)
			\/ (split <= k /\ kv_appears_in_tree k v right))).
Proof.
  induction counter.
  Case "counter = 0".
    intros.
    inversion H.
    simpl in H1.
    destruct kpl. simpl in H5. exfalso. omega.
    destruct p. inversion H1.
  Case "counter = S counter".
    intros.
    simpl in H2.
    remember (find_subtree k kpl).
    destruct o.
    SCase "find_subtree = Some p".
      destruct p.
      remember (insert' counter k v b0).
      destruct p.
      symmetry in Heqp.
      assert (counter = height b0).
          symmetry in Heqo.
          apply find_subtree_impl_kpl_app in Heqo.
          destruct Heqo. destruct H3. inversion H3.
          inversion H.
          apply height_of_parent_one_bigger with (k:=n)(v:=b0)(l1:=witness)(l2:=witness0) in H12;
            try assumption.
          rewrite <- H12 in H1.
          omega.
      destruct b0.
      SSCase "child was a leaf".
        remember (bptLeaf b X l) as child.
        symmetry in Heqo.
        assert (valid_bplustree b X child) by (apply child_is_valid_bplustree with (k := k) (key := n) (kpl := kpl); assumption).
        assert (~appears_in_tree k child) by (apply not_appears_in_subtree_when_not_appears_in_tree_and_found with (key := n) (kpl := kpl); assumption).
        assert (~appears_in_kvl k l).
          unfold not. intro. 
          apply H5.
          rewrite Heqchild.
          constructor.
          apply H6.
        destruct o.
        SSSCase "child overflowed".
          destruct p.
          remember (ble_nat (length (insert_into_list n b1 (insert_into_list n0 b0 kpl))) (b * 2 + 1)) as fits_here.
          destruct fits_here.
          SSSSCase "overflow fits on this level".
            assert (insert' counter k v child = (b1, Some (n0, b0))) by assumption.
            inversion H2. clear H2. clear H9. clear H10. clear Heqfits_here.
            left. split. reflexivity.
            rewrite Heqchild in Heqp. 
            rewrite insert'_leaf_disregards_counter in Heqp.
            remember (insert_leaf b k v l).
            destruct p.
            destruct o; [ | inversion Heqp].
            assert (l1 <> []).
              apply insert_leaf_split_never_empty in Heqp0.
              intuition.
              inversion H.
              assumption.
            destruct l1. exfalso. apply H2. reflexivity.
            destruct p. clear H2.
            symmetry in Heqp0.
            assert (l0 ++ (n1,x)::l1 = insert_into_list k v l).
              apply insert_leaf_split_preserves_list in Heqp0.
              symmetry in Heqp0.
              assumption.
            apply insert_leaf_impl_appears in Heqp0; try (inversion H; rewrite Heqchild in H4; inversion H4; assumption).
            inversion Heqp.
            rewrite H10 in *.
            assert (n <= k).
              inversion H.
              assert (1 <= length kpl) by omega.
              eapply find_subtree_returns_a_lesser_key. 
                apply H20.
                apply H18.
                apply Heqo.
            assert (n < n0).
              rewrite H3 in H7.
              inversion H.
              eapply insert'_overflow_impl_greater_key.
                apply H13.
                apply H.
                apply Heqo.
                apply H7.
                assumption.
            assert (kvl_sorted((insert_into_list n (bptLeaf b X l0) (insert_into_list n0 (bptLeaf b X ((n0, x) :: l1)) kpl)))).
              apply insert_preserves_sort. apply insert_preserves_sort.
              inversion H.
              apply H20.
            assert(find_subtree k kpl = Some (n, child)) by assumption.
            apply find_subtree_impl_kpl_app in H14. 
            do 2 destruct H14.
            inversion H14. clear H14.
            rewrite H15. rewrite H15 in H13.
            destruct witness0.
            SSSSSCase "leaf was at the end of the node".
              rewrite insert_into_list_last_twice in *; try (rewrite H15 in H; inversion H; assumption).
              remember (blt_nat k n0) as in_left.
              destruct in_left; symmetry in Heqin_left; [ apply blt_nat_true in Heqin_left | apply blt_nat_false in Heqin_left ].
              SSSSSSCase "n <= k < n0".
                assert (n <= k < n0) by omega.
                inversion Heqp0.
                SSSSSSSCase "appears in left leaf".
                  rewrite H9. rewrite H9 in H13.
                  rewrite H11. rewrite H11 in H13.
                  assert (kv_appears_in_tree k v b1).
                    rewrite <- H9.
                    apply kv_ait_leaf.
                    apply H17.
                  eapply kv_appears_in_tree_when_appears_in_subtree with (l2 := []).
                    apply H18.
                    apply H14.
                    apply H13.
                SSSSSSSCase "appears in right leaf (bogus)".
                  destruct H17. inversion H17. inversion H18.
                  rewrite <- H21 in H19. clear H17. clear H18. clear H21.
                  assert (kvl_sorted ((n0,x)::l1)).
                    assert (kvl_sorted (l0 ++ (n0, x) :: l1)).
                      rewrite Heqchild in H4. inversion H4.
                      rewrite H2. apply insert_preserves_sort. assumption. 
                      apply kvl_sorted_app in H17.
                    inversion H17.
                    assumption.
                  assert (~appears_in_kvl k ((n0,x)::l1)).
                    assert (kvl_sorted ((n0, x) :: l1)) by assumption.
                    apply sorted_all_keys_above_cons in H18.
                    eapply key_smaller_than_all_keys_does_not_appear.
                      apply H17.
                      apply H18.
                      omega.
                  exfalso. 
                  apply H18. 
                  apply kv_appears_in_kvl_impl_appears_in_kvl in H19. 
                  apply H19.
              SSSSSSCase "n0 <= k".
                assert (n0 <= k) by omega.
                inversion Heqp0.
                SSSSSSSCase "appears in left (bogus)".
                  assert (kvl_sorted (l0 ++ (n0, x) :: l1)).
                    rewrite Heqchild in H4. inversion H4.
                    rewrite H2. apply insert_preserves_sort. assumption. 
                  assert (kvl_sorted l0).
                    apply kvl_sorted_app in H18.
                    inversion H18.
                    assumption.
                  assert (~appears_in_kvl k l0).
                    apply sorted_all_keys_below_app_cons in H18.
                    eapply key_greater_than_all_keys_does_not_appear.
                      apply H19.
                      apply H18.
                      omega.
                  exfalso. apply H20.
                  apply kv_appears_in_kvl_impl_appears_in_kvl in H17.
                  apply H17.
                SSSSSSSCase "appears in right".
                  destruct H17. inversion H17. inversion H18.
                  rewrite <- H21 in H19. clear H17. clear H18. clear H21.
                  rewrite H11. rewrite H11 in H13.
                  rewrite H9. rewrite H9 in H13.
                  assert (kv_appears_in_tree k v b0).
                    rewrite <- H11.
                    apply kv_ait_leaf.
                    apply H19.
                  destruct witness.
                  SSSSSSSSCase "witness = []".
                    simpl. apply kv_ait_node_last; try assumption.
                  SSSSSSSSCase "witness = p::witness".
                    destruct p. simpl.
                    remember (witness ++ [(n,b1)]) as witness'.
                    assert ((n2, b2) :: witness ++ [(n, b1), (n0, b0)] = (n2, b2) :: witness' ++ [(n0, b0)]).
                      rewrite Heqwitness'. rewrite <- app_assoc.
                      simpl. reflexivity. 
                  rewrite H18.
                  eapply kv_appears_in_tree_when_appears_in_last_subtree.
                    apply H17.
                    apply H14.
                    rewrite <- H18. apply H13.
            SSSSSCase "leaf was in the middle of the node".
              destruct p.
              inversion H16. inversion H14.
              do 3 destruct H14. inversion H14. clear H14. clear H16.
              inversion H17. rewrite H16 in *. rewrite H19 in *. rewrite H20 in *.
              clear H17. clear H16. clear H19. clear H20.
              assert (n < witness1).
                inversion H.
                rewrite H15 in H23.
                apply kvl_sorted_app with (l2 := (n, child) :: (witness1, witness2) :: witness3) in H23.
                inversion H23.
                inversion H26.
                apply blt_nat_true in H33.
                omega.
              assert (n0 < witness1).
                inversion H.
                eapply insert'_overflow_impl_lesser_than_next.
                  rewrite H15 in Heqo. apply Heqo.
                  rewrite H3 in H7. apply H7.
                  rewrite H15 in H24. apply H24.
              assert (n < n0 < witness1).
                omega.
              rewrite insert_into_list_middle_twice in *; try (rewrite H15 in H; inversion H; assumption).
              remember (blt_nat k n0) as in_left.
              destruct in_left; symmetry in Heqin_left; [ apply blt_nat_true in Heqin_left | apply blt_nat_false in Heqin_left ].
              SSSSSSCase "n <= k < n0".
                assert (n <= k < n0) by omega.
                inversion Heqp0.
                SSSSSSSCase "appears in left leaf".
                  rewrite H9. rewrite H9 in H13.
                  rewrite H11. rewrite H11 in H13.
                  assert (kv_appears_in_tree k v b1).
                    rewrite <- H9.
                    apply kv_ait_leaf.
                    apply H20.
                  eapply kv_appears_in_tree_when_appears_in_subtree with (l2 := ((witness1, witness2)::witness3)).
                    apply H21.
                    apply H19.
                    apply H13.
                SSSSSSSCase "appears in right leaf (bogus)".
                  destruct H20. inversion H20. inversion H21.
                  rewrite <- H24 in H22. clear H20. clear H21. clear H24.
                  assert (kvl_sorted ((n0,x)::l1)).
                    assert (kvl_sorted (l0 ++ (n0, x) :: l1)).
                      rewrite Heqchild in H4. inversion H4.
                      rewrite H2. apply insert_preserves_sort. assumption. 
                      apply kvl_sorted_app in H20.
                    inversion H20.
                    assumption.
                  assert (~appears_in_kvl k ((n0,x)::l1)).
                    assert (kvl_sorted ((n0, x) :: l1)) by assumption.
                    apply sorted_all_keys_above_cons in H21.
                    eapply key_smaller_than_all_keys_does_not_appear.
                      apply H20.
                      apply H21.
                      omega.
                  exfalso. 
                  apply H21. 
                  apply kv_appears_in_kvl_impl_appears_in_kvl in H22. 
                  apply H22.
              SSSSSSCase "n0 <= k".
                assert (n0 <= k) by omega.
                inversion Heqp0.
                SSSSSSSCase "appears in left (bogus)".
                  assert (kvl_sorted (l0 ++ (n0, x) :: l1)).
                    rewrite Heqchild in H4. inversion H4.
                    rewrite H2. apply insert_preserves_sort. assumption. 
                  assert (kvl_sorted l0).
                    apply kvl_sorted_app in H21.
                    inversion H21.
                    assumption.
                  assert (~appears_in_kvl k l0).
                    apply sorted_all_keys_below_app_cons in H21.
                    eapply key_greater_than_all_keys_does_not_appear.
                      apply H22.
                      apply H21.
                      omega.
                  exfalso. apply H23.
                  apply kv_appears_in_kvl_impl_appears_in_kvl in H20.
                  apply H20.
                SSSSSSSCase "appears in right".
                  destruct H20. inversion H20. inversion H21.
                  rewrite <- H24 in H22. clear H20. clear H21. clear H24.
                  rewrite H11. rewrite H11 in H13.
                  rewrite H9. rewrite H9 in H13.
                  assert (kv_appears_in_tree k v b0).
                    rewrite <- H11.
                    apply kv_ait_leaf.
                    apply H22.
                  assert (n0 <= k < witness1) by omega.
                  remember (witness ++ [(n, b1)]) as witness'.
                  assert (witness ++ (n, b1) :: (n0, b0) :: (witness1, witness2) :: witness3 = witness' ++ (n0, b0) :: (witness1, witness2) :: witness3). 
                    rewrite Heqwitness'. rewrite <- app_assoc. simpl.
                    reflexivity.
                  rewrite H23.
                  eapply kv_appears_in_tree_when_appears_in_subtree.
                    apply H20.
                    apply H21.
                    rewrite <- H23. apply H13.
          SSSSCase "overflow doesnt fit on this level".
            right.
            remember (insert_into_list n b1 (insert_into_list n0 b0 kpl)) as kpl'.
            rewrite Heqchild in H4.
            assert (length kpl' > b * 2 + 1).
              symmetry in Heqfits_here.
              apply ble_nat_false in Heqfits_here.
              omega. 
            clear Heqfits_here.
            assert (insert' counter k v child = (b1, Some (n0, b0))) by (subst; assumption).
            rewrite Heqchild in H8. 
            rewrite insert'_leaf_disregards_counter in H8.
            remember (insert_leaf b k v l).
            destruct p.
            destruct o; [ | inversion Heqp; inversion H8].
            assert (l1 <> []).
              apply insert_leaf_split_never_empty in Heqp0.
              intuition.
              inversion H.
              assumption.
            destruct l1. exfalso. apply H9. reflexivity.
            destruct p. clear H9.
            symmetry in Heqp0.
            assert (l0 ++ (n1,x)::l1 = insert_into_list k v l).
              apply insert_leaf_split_preserves_list in Heqp0.
              symmetry in Heqp0.
              assumption.
            inversion H8. rewrite H12 in *. clear H12. clear n1.
            symmetry in H11. symmetry in H13. clear H8.
            apply insert_leaf_impl_appears in Heqp0; try (subst; inversion H4; assumption).
            rewrite H3 in Heqp.
            remember (cut_list_left (b + 1) kpl') as ll.
            remember (cut_list_right(b + 1) kpl') as rl.
            assert (rl <> []).
              assert (length kpl' > b + 1) by omega.
              apply cut_right_not_nil in H8.
              rewrite Heqrl. assumption.
            destruct rl. exfalso. apply H8. reflexivity.
            destruct p.            
            
            inversion H2.
            exists n1. exists (bptNode b X ((0, b2)::rl)).
            split. reflexivity. clear H12. clear H14.
            remember (blt_nat k n0) as in_left.
            destruct in_left; symmetry in Heqin_left; [ apply blt_nat_true in Heqin_left | apply blt_nat_false in Heqin_left ].
            SSSSSCase "it should be in the left tree".
              inversion Heqp0.
              SSSSSSCase "it does appear in the left tree".
                assert (kv_appears_in_tree k v b1).
                  rewrite H11.
                  apply kv_ait_leaf.
                  assumption.
                eapply insert'_impl_appears_overflow_left.
                  apply H.
                  apply Heqp.
                  apply Heqo.
                  apply Heqkpl'.
                  apply H7.
                  apply Heqrl.
                  apply Heqll.
                  omega.
                  apply H12.
              SSSSSSCase "it does not appear in the left tree".
                destruct H10. inversion H10. inversion H12.
                rewrite <- H16 in H14. clear H10. clear H12. clear H16.
                assert (kvl_sorted (l0 ++ (n0,x)::l1)).
                  rewrite H9. apply insert_preserves_sort.
                  inversion H4. assumption.
                apply kvl_sorted_app in H10.
                inversion H10.
                assert (~appears_in_kvl k ((n0,x)::l1)).
                  assert (kvl_sorted ((n0, x) :: l1)) by assumption.
                  apply sorted_all_keys_above_cons in H16.
                  eapply key_smaller_than_all_keys_does_not_appear.
                    apply H15.
                    apply H16.
                    omega.
                exfalso. apply H16. apply kv_appears_in_kvl_impl_appears_in_kvl in H14.
                apply H14.
            SSSSSCase "it should be in the right tree".
              assert (n0 <= k) by omega.
              inversion Heqp0.
              SSSSSSCase "but it appears in the left tree".
                assert (kvl_sorted (l0 ++ (n0,x)::l1)).
                  rewrite H9.
                  apply insert_preserves_sort.
                  inversion H4.
                  apply H17.
                assert (kvl_sorted (l0 ++ (n0,x)::l1)) by assumption.
                apply sorted_all_keys_below_app_cons in H15.
                assert (~appears_in_kvl k l0).
                  eapply key_greater_than_all_keys_does_not_appear.
                    apply kvl_sorted_app in H14. inversion H14.
                      apply H16.
                    apply H15.
                    omega.
                exfalso. apply H16. apply kv_appears_in_kvl_impl_appears_in_kvl in H12.
                apply H12.
              SSSSSSCase "and it does".
                destruct H12. inversion H12. inversion H14.
                rewrite <- H17 in H15. clear H12. clear H14. clear H17.
                assert (kv_appears_in_tree k v b0).
                  rewrite H13.
                  apply kv_ait_leaf.
                  assumption.
                eapply insert'_impl_appears_overflow_right.
                  apply H.
                  apply Heqp.
                  apply Heqo.
                  apply Heqkpl'.
                  apply H7.
                  apply Heqrl.
                  apply Heqll.
                  apply H10.
                  apply H12.
        SSSCase "child didn't overflow".
          rewrite Heqchild in Heqp.
          unfold insert' in Heqp. simpl in Heqp.
          left.
          rewrite insert'_leaf_disregards_counter in Heqp.
          remember (insert_leaf b k v l);
          destruct p; destruct o.
          assert (l1 <> []).
            apply insert_leaf_split_never_empty in Heqp0.
            intuition.
            inversion H.
            assumption.
          destruct l1. exfalso. apply H7. reflexivity.
          destruct p. inversion Heqp.
          inversion Heqp. clear Heqp.
          symmetry in Heqo.
          assert (kv_appears_in_tree k v (bptLeaf b X l0)).
            inversion Heqchild in H4. inversion H4.
            assert (length l < b*2).
              symmetry in Heqp0.
              apply insert_leaf_not_split_impl_space_left in Heqp0.
              omega.
              apply H6.
            constructor.
            symmetry in Heqp0.
            apply insert_leaf_impl_appears_normal in Heqp0; try assumption.
          inversion H2.
          split. reflexivity.
          rewrite H8 in H7.
          eapply insert'_impl_appears_normal; try assumption.
            symmetry in Heqo. apply Heqo.
            assumption.
      SSCase "child was a node".
        remember (bptNode b X l) as child.
         
        assert (valid_bplustree b X child) by (symmetry in Heqo; apply child_is_valid_bplustree with (k := k) (key := n) (kpl := kpl); assumption).
        assert (~appears_in_tree k child) by (symmetry in Heqo; apply not_appears_in_subtree_when_not_appears_in_tree_and_found with (key := n) (kpl := kpl); assumption).
        rewrite Heqchild in Heqp.
        assert (insert' counter k v (bptNode b X l) = (b1, o)) by assumption.
        apply IHcounter in Heqp; try (rewrite <- Heqchild; assumption).
        clear IHcounter.
        
        destruct o.
        SSSCase "child overflowed".
          destruct p.
          inversion Heqp; clear Heqp.
          inversion H7. inversion H8. 
          remember (ble_nat (length (insert_into_list n b1 (insert_into_list n0 b0 kpl))) (b * 2 + 1)) as fits_here.
          destruct fits_here.
          SSSSCase "overflow fit on this level".
            clear Heqfits_here.
            inversion H2.
            do 2 destruct H7.
            inversion H7. clear H7.
            inversion H11; clear H11; left; split; try reflexivity; 
              inversion H7; clear H7;
              inversion H8; clear H8.
            SSSSSCase "appears in left subtree".
              remember (insert_into_list witness witness0 kpl) as kpl'.
              remember (insert_into_list n b1 kpl') as kpl''.
              assert (find_subtree k kpl'' = Some (n, b1)).
                symmetry in Heqo.
                apply find_subtree_after_inserting_greater_element with (k2:= witness) (t2:= witness0) in Heqo; try assumption.
                rewrite <- Heqkpl' in Heqo.
				rewrite Heqkpl''.
                apply find_subtree_after_replace with (t1 := child); try assumption.
                rewrite Heqkpl'.
                apply insert_preserves_sort.
                
                inversion H. assumption.
                inversion H. assert (1 <= length kpl) by omega. assumption.
                inversion H. assumption.
              assert (kvl_sorted kpl'').
                rewrite Heqkpl''.
                apply insert_preserves_sort.
                rewrite Heqkpl'.
                apply insert_preserves_sort.
                inversion H. assumption.
              assert (2 <= length kpl'').
                assert (length kpl' <= length kpl'').
                  rewrite Heqkpl''.
                  apply insert_into_list_length_gt_iil_length.
                  rewrite Heqkpl'.
                  apply insert_preserves_sort.
                  inversion H.
                  assumption.
                assert (length kpl <= length kpl').
                  rewrite Heqkpl'.
                  apply insert_into_list_length_gt_iil_length.
                  inversion H.
                  assumption.
                inversion H.
                omega.
              
              apply kv_appears_in_tree_when_appears_in_subtree_and_found with (kpl := kpl'') (subtree := b1) (key := n); try reflexivity; try assumption.
            SSSSSCase "appears in right subtree".
              symmetry in Heqo.
              assert (find_subtree k kpl = Some (n, child)) by assumption.
              apply find_subtree_impl_kpl_app in H7.
              do 2 destruct H7. inversion H7. clear H7.
              assert (n <= k).
                inversion H.
                assert (1 <= length kpl) by omega.
                apply find_subtree_returns_a_lesser_key in Heqo; assumption.
              assert (n < witness).
                rewrite H3 in H6. rewrite H13 in H6. rewrite H14 in H6.
                rewrite <- Heqchild in H6.
                inversion H.
                eapply insert'_overflow_impl_greater_key.
                  apply H17.
                  apply H.
                  apply Heqo.
                  apply H6. 
                  assumption.
             destruct witness2.
              SSSSSSCase "subtree was last in the node".
                clear H15.
                rewrite H8.
                inversion H. rewrite H8 in H23.
                assert (kvl_sorted (insert_into_list n b1 (insert_into_list witness witness0 (witness1 ++ [(n, child)])))).
                  apply insert_preserves_sort. apply insert_preserves_sort.
                  assumption.
                rewrite insert_into_list_last_twice in *; try assumption.
                destruct witness1.
                  apply kv_ait_node_last; assumption.
                  destruct p.
                  rewrite <- app_comm_cons.
                  remember (witness1 ++ [(n, b1)]).
                  replace ((n1, b2) :: witness1 ++ [(n, b1), (witness, witness0)]) with ((n1, b2)::l0 ++ [(witness, witness0)]).
                  apply kv_appears_in_tree_when_appears_in_last_subtree; try assumption.
                  rewrite Heql0.
                  rewrite <- app_assoc. simpl.
                  assumption.
                  rewrite Heql0. rewrite <- app_assoc. reflexivity.
              SSSSSSCase "subtree was not last in the node".
                inversion H15. inversion H17.
                do 3 destruct H17. destruct p.
                inversion H17. clear H17.
                inversion H18. clear H18.
                rewrite <- H20 in *. clear H20. clear witness3.
                clear H21. clear witness4.
                clear H22. clear witness5.
                
                rewrite H8.
                assert (kvl_sorted(witness1 ++ (n, child) :: (n1, b2) :: witness2)).
                  inversion H.
                  rewrite <- H8.
                  assumption. 
                assert (kvl_sorted(insert_into_list n b1 (insert_into_list witness witness0 (witness1 ++ (n, child) :: (n1, b2) :: witness2)))).
                  apply insert_preserves_sort. apply insert_preserves_sort. 
                  assumption.
                assert (n < witness < n1) by omega.
                rewrite insert_into_list_middle_twice in *; try assumption.
                remember (witness1 ++ [(n, b1)]).
                assert (witness1 ++ (n, b1) :: (witness, witness0) :: (n1, b2) :: witness2 = l0 ++ (witness, witness0)::(n1,b2)::witness2).
                  rewrite Heql0. rewrite <- app_assoc. simpl. reflexivity.
				remember ((witness1 ++ (n, b1) :: (witness, witness0) :: (n1, b2) :: witness2)) as kpl'.
				assert (2 <= length kpl').
				  assert (S (length kpl) = length kpl').
				    rewrite H21. rewrite H8.
				    rewrite Heql0.
				    repeat rewrite app_length. simpl.
				    omega.
				  inversion H.
				  omega.
				assert (witness <= k < n1) by omega.
				assert (find_subtree k kpl' = Some (witness, witness0)).
				  rewrite H21 in H18.
				  apply find_subtree_key_in_middle with (sk := k) in H18.
				  apply H18 in H23.
				  rewrite <- H21 in H23.
				  assumption.
				eapply kv_appears_in_tree_when_appears_in_subtree_and_found.
				  apply H22.
				  apply H18.
				  reflexivity.
				  apply H24.
				  apply H12.
          SSSSCase "overflow didn't fit on this level".
            right.
            do 2 destruct H7. inversion H7. clear H7. inversion H8. clear H8.
            rewrite H10 in *. clear H10. clear n0.
            rewrite H11 in *. clear H11. clear b0.
            remember (insert_into_list n b1 (insert_into_list witness witness0 kpl)) as kpl'.
            assert (find_subtree k kpl = Some (n, child)) by (symmetry in Heqo; assumption).
            apply find_subtree_impl_kpl_app in H7.
            do 2 destruct H7. inversion H7. clear H7.
            symmetry in Heqfits_here. apply ble_nat_false in Heqfits_here.
            assert (length kpl' > b + 1) by omega.
            apply cut_right_not_nil in H7.
            remember (cut_list_right (b + 1) kpl') as right.
            destruct right. exfalso. apply H7. reflexivity.
            destruct p.
            exists n0. exists (bptNode b X ((0, b0) :: right)).
            split. inversion H2. reflexivity.
            
            inversion H9; clear H9; inversion H11; clear H11.
            SSSSSCase "insert happened in the normal child".
              inversion H2.
              eapply insert'_impl_appears_overflow_left with (kpl := kpl); try (subst; assumption).
                rewrite H3 in H6. rewrite <- Heqchild in H6.
                  apply H6.
                symmetry in Heqo.
                  apply Heqo.
                apply Heqkpl'.
                omega.
                apply Heqright.
                reflexivity.
                omega.
                apply H12.
            SSSSSCase "insert happened in the overflow child".
              inversion H2.
              eapply insert'_impl_appears_overflow_right with (kpl := kpl); try (subst; assumption). 
                rewrite H3 in H6. rewrite <- Heqchild in H6.
                  apply H6.
                symmetry in Heqo.
                  apply Heqo.
                apply Heqkpl'.
                omega.
                apply Heqright.
                reflexivity.
                omega.
                apply H12.
        SSSCase "child didn't overflow".
          inversion Heqp.
          SSSSCase "appears in left subtree".
            inversion H2. clear H10.
            inversion H7. clear H7. clear H8.
            left. split. reflexivity.
            eapply insert'_impl_appears_normal; try assumption.
              symmetry in Heqo. apply Heqo.
              assumption.
          SSSSCase "appears in right subtree (bogus)".
            do 2 destruct H7. inversion H7.
            inversion H8.
    SCase "find_subtree = None".
      apply find_subtree_finds_a_subtree with (sk := k) in H.
      do 2 destruct H. rewrite H in Heqo. inversion Heqo.
Qed.

Theorem insert_impl_appears : forall {X: Type} {b: nat} (t t1: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> 
  ~appears_in_tree k t -> 
  insert k v t = t1 -> 
  kv_appears_in_tree k v t1.
Proof.
  intros.
  induction H.
  Case "leaf".
	unfold insert in H1.  unfold insert' in H1. simpl in H1. remember (insert_leaf b k v kvl) as il. 
	destruct il. destruct o.
	SCase "insert split".
	  assert ((l, Some l0) = insert_leaf b k v kvl) by assumption.
	  apply insert_leaf_split_never_empty  in H4.
	  destruct l0. 
	    inversion H4. exfalso. apply H6. reflexivity.
	  destruct p.
	    
	  symmetry in Heqil. assert (insert_leaf b k v kvl = (l, Some ((n,x)::l0))) by assumption.
	  apply insert_leaf_impl_appears in Heqil; try assumption.
	    rewrite <- H1. apply kv_appears_in_split_node_appears_in_lists. destruct Heqil. 
	    apply insert_leaf_preserves_sort in H5; assumption; assumption.
	    apply insert_leaf_preserves_sort in H5; assumption; assumption.
	    simpl. reflexivity.
	    destruct Heqil. left. assumption.
	    inversion H6. right. destruct H6. inversion H7. inversion H8. rewrite H11. assumption.
	    unfold not. intro. apply H0. apply ait_leaf. apply H6.
	    assumption.
	SCase "insert_normal".
	  symmetry in Heqil. apply insert_leaf_impl_appears_normal in Heqil; try assumption. rewrite <- H1. 
	  apply kv_ait_leaf; try assumption. unfold not. intro. unfold not in H0.
	  eapply appears_kvl_appears_leaf_tree in H4. apply H0. apply H4. 
	  apply insert_leaf_not_split_impl_space_left in Heqil. assumption.
	  unfold not. unfold not in H0. intros. apply H0. apply ait_leaf. assumption.
  Case "node". 
    unfold insert in H1.
    remember (insert' (height (bptNode b X kpl)) k v (bptNode b X kpl)).
    destruct p. 
    symmetry in Heqp.
    apply insert'_impl_appears in Heqp; try assumption; try reflexivity.
    
    destruct o. 
    SCase "node overflow".
      destruct p.
      inversion Heqp. destruct H9.  inversion H9. do 3 destruct H9.
      inversion H9. subst. destruct H10.
      SSCase "appears in left".
        apply kv_ait_node_here. destruct H1. assumption. omega.
      SSCase "appears in right".
		destruct H1.
		apply kv_ait_node_last. assumption. omega.
    SCase "node didn't overflow".
      inversion Heqp. 
      SSCase "appears in left".
        subst. apply H9.
      SSCase "appears in right (bogus)".
        do 2 destruct H9. inversion H9.
        inversion H10.
    
    constructor; try assumption.
Qed.
    




