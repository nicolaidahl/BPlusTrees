Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.
Require Export ValidBPlusTree.
Require Export AppearsInKVL.
Require Export AppearsInTree.
Require Export ElementAtIndexProofs.
Require Export SplitCutList.
Require Export InsertProofs.
  
Lemma list_of_length_b_implies_element_at_b : forall (X: Type) (b: nat) (kvl: list (nat* X)),
  kvl <> [] -> b < length kvl -> 
  exists k, exists v, element_at_index b kvl = Some(k, v).
Proof.
  intros. 
  generalize dependent b.
  induction kvl.
  Case "kvl = 0". 
    apply ex_falso_quodlibet. apply H. reflexivity. 
    intros.
    destruct b.
      simpl. destruct a. exists n. exists x. reflexivity.
      simpl. simpl in H0. 
      assert (kvl <> []).
        destruct kvl. simpl in H0. inversion H0. inversion H2.
        unfold not. intro. inversion H1.
      apply IHkvl.
        apply H1.
        omega.
Qed.

Theorem split_insert_right : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index (pred b) leaf = Some (kb, vb) -> 
  kb < k -> length leaf = mult b 2 -> 
  insert_leaf b k v leaf = (left, Some kvl) -> appears_in_kvl k kvl.
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
      subst. apply ex_falso_quodlibet. apply H1. apply ai_here.
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
         
         apply appears_in_kvl_dist_app with (k := k) in Heqsplit.
         inversion Heqsplit. clear Heqsplit. 
         SSSSCase "appears_in_kvl n left".
           (* This case is bogus, needs an inversion *)
           apply split_list_left_length in H5.
           simpl in H4. 
                      
           apply element_unchanged_by_inserting_greater_key with (k3 := k) (v3 := v) in H2; try assumption.
           
           apply element_at_index_pred_b_implies_left_below_S_b with (l1 := left) (l2 := kvl) in H2; try assumption.
           apply key_greater_than_all_keys_does_not_appear_ble with (k:=k) in H2; try assumption.
           (* We've found our inversion - k both appears and does not appear in left *)
           apply ex_falso_quodlibet. apply H2. assumption.
           
            
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
           unfold not. intro. apply H1. apply ai_later. assumption.
           reflexivity.
         SSSSCase "appears_in_kvl n kvl".
           assumption.
         apply ai_later.
         apply insert_into_list_appears.
         unfold not. intro. apply H1. apply ai_later. assumption.
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



Theorem split_insert_left : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index (pred b) leaf = Some (kb, vb) -> 
  k < kb -> length leaf = mult b 2 ->
  insert_leaf b k v leaf = (left, Some kvl) -> appears_in_kvl k left.
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
           apply ai_later. apply H8.
           reflexivity.
         SSSSCase "left = p::left". 
           destruct p.
           rewrite <- app_comm_cons in Heqsplit. inversion Heqsplit.
           apply appears_in_kvl_dist_app with (k := k) in H11.
           destruct H11.
           SSSSSCase "appears in left".
             apply ai_later. apply H8.
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
             
             apply ex_falso_quodlibet. apply H2. assumption.
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
             unfold not. intro. apply H1. apply ai_later. assumption.
             reflexivity.
           apply insert_into_list_appears.
           unfold not. intro. apply H1. apply ai_later. assumption.           
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
              rewrite <- app_comm_cons in Heqsplit. inversion Heqsplit. apply ai_here.
              omega.
Qed.


Theorem insert_leaf_normal : forall {X: Type} {b: nat} (leaf left: list (nat * X)) (k: nat) (v: X),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> length leaf < mult b 2 ->
  insert_leaf b k v leaf = (left, None) -> appears_in_kvl k left.
Proof.
  intros. 
  
  destruct leaf.
  Case "leaf = []".
    intros.
    destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
    compute in H3. inversion H3. apply ai_here.
  Case "leaf = a::leaf".
    intros.
    destruct p.
    remember (beq_nat n k) as neqk.
    destruct neqk; symmetry in Heqneqk; [apply beq_nat_true_iff in Heqneqk|apply beq_nat_false_iff in Heqneqk].
    SCase "n = k".
      rewrite insert_leaf_cons_eq in H3.
      inversion H3. apply ai_here. apply H. apply H0. 
      rewrite Heqneqk. reflexivity.
      simpl. simpl in H2. omega.
    SCase "n <> k".
      remember (ble_nat n k) as nlek.
      destruct nlek; symmetry in Heqnlek; [apply ble_nat_true in Heqnlek|apply ble_nat_false in Heqnlek].
      SSCase "n <= k".
       apply le_lt_or_eq_iff in Heqnlek. inversion Heqnlek.
       SSSCase "n < k".
         rewrite insert_leaf_cons_gt in H3.
         inversion H3. apply ai_later.
         apply insert_into_list_appears.
         apply H.
         apply H0.
         omega.
         simpl in H2. simpl. omega. 
       SSSCase "n = k".
         apply ex_falso_quodlibet. apply Heqneqk. apply H4.
      SSCase "n > k".
        rewrite insert_leaf_cons_lt in H3.
        inversion H3. apply ai_here.
        apply H.
        apply H0.
        omega.
        simpl in H2. simpl. omega.
Qed.




Theorem insert_leaf_works : forall {X: Type} {b: nat} (k: nat) (v: X) (leaf left: list (nat * X)) (rightOption: option (list (nat * X))),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> 
  length leaf <= mult b 2 ->
  insert_leaf b k v leaf = (left, rightOption) ->
  appears_in_kvl k left \/ (exists right, rightOption = Some(right) /\ appears_in_kvl k right).
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
      eapply insert_leaf_normal. 
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
            eapply split_insert_right.
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
        eapply split_insert_left.
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



Lemma insert_leaf_shaddow : forall (X: Type) (b: nat) (n: nat) (v x: X) (kvl: list (nat * X)),
  b <> 0 -> length ((n,x) :: kvl) <= mult b 2 -> insert_leaf b n v ((n, x) :: kvl) = ((n, v) :: kvl, None).
Proof.
  intros.
  
  unfold insert_leaf. unfold insert_into_list.
  rewrite ble_nat_symm. rewrite <- beq_nat_refl.
  remember (ble_nat (length ((n,v) :: kvl)) (b * 2)) as lb2.
  destruct lb2.
  reflexivity.
  symmetry in Heqlb2. apply ble_nat_false in Heqlb2.
  unfold not in Heqlb2.
  apply ex_falso_quodlibet.
  apply Heqlb2. simpl in H0. simpl. apply H0.
Qed.

Theorem insert_leaf_split_never_empty: forall {X: Type} b k (v: X) l l1 l2,
  b <> 0 ->
  (l1, Some l2) = insert_leaf b k v l -> l1 <> [] /\ l2 <> [].
Proof. 
  intros.
  destruct l.
  Case "l = []".
    unfold insert_leaf in H0.
    simpl in H0. remember (b*2). destruct n.
    apply ex_falso_quodlibet. omega.
    inversion H0.
  Case "l = p::l". destruct p.
    unfold insert_leaf in H0.
    simpl in H0.
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        simpl in H0. replace (b*2) with (S(S(pred(b)*2))) in H0 by omega.
        remember (ble_nat (length l) (S (pred b * 2))) as tl.
        destruct tl. inversion H0.
        inversion H0.
        symmetry in Heqtl. apply ble_nat_false in Heqtl.
        split.
          apply cut_left_not_nil; simpl; try assumption; try omega.
          apply cut_right_not_nil; simpl; try assumption; try omega.
      SSCase "k < n".
        remember (ble_nat (length ((k, v) :: (n, x) :: l)) (b * 2)) as tl.
        destruct tl. inversion H0.
        symmetry in Heqtl. apply ble_nat_false in Heqtl. simpl in Heqtl.
        inversion H0.
        split.
          apply cut_left_not_nil; simpl; try assumption; try omega. 
          apply cut_right_not_nil; simpl; try assumption; try omega.
    SCase "k > n".
      remember (ble_nat (length ((n, x) :: insert_into_list k v l)) (b * 2)) as tl.
      destruct tl. inversion H0.
      inversion H0.
      symmetry in Heqtl. apply ble_nat_false in Heqtl. simpl in Heqtl.
      split.
          apply cut_left_not_nil; simpl; try assumption; try omega. 
          apply cut_right_not_nil; simpl; try assumption; try omega.
Qed.





Lemma insert'_not_split_impl_space_left: forall {X: Type} (b: nat) k (v:X) kpl tree,
  b <> 0 ->
  ~ appears_in_tree k (bptNode b X kpl) ->
  kvl_sorted kpl ->
  insert' (height (bptNode b X kpl)) k v (bptNode b X kpl) = (tree, None) ->
  length kpl < S (b*2).
Proof.
  admit.
Admitted.
(*
  intros.
  destruct tree.
    (* This wont happen, because insert' on a node, can't return a leaf *)
    admit.

  induction kpl.
  Case "kpl = []".
    simpl. omega.
  Case "kpl = a::kpl". destruct a. generalize H2.
    set (insert' (height bptNode b X l) k v (bptNode b X ((n, b0) :: kpl))) as test.
    intro.
    hnf in test.
    destruct kpl.
      simpl. omega.
      destruct p.
      remember (ble_nat n k && blt_nat k n0).
      destruct b2. hnf in test.
      remember (insert' k v b0).
      destruct p. destruct o. destruct p.
      SCase "insert in child overflowed".
        admit.
      SCase "insert in child had room".
        simpl in test. remember (ble_nat n n).  destruct b3.
        remember (beq_nat n n). destruct b3.
        
        admit.
        
        
        rewrite <- beq_nat_refl in Heqb0. inversion Heqb0.
        rewrite ble_nat_symm in Heqb3. inversion Heqb3.
        
      
        
      destruct kpl.
      admit.
      
  simpl.
    admit.
Admitted.
*)



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

Theorem insert'_normal : forall {X: Type} {b: nat} (kpl: list (nat * bplustree b X)) (tree: bplustree b X) (k: nat) (v: X),
  b <> 0 -> valid_bplustree b X (bptNode b X kpl) -> not (appears_in_tree k (bptNode b X kpl)) -> length kpl < S (mult b 2) ->
  insert' (height (bptNode b X kpl)) k v (bptNode b X kpl) = (tree, None) -> appears_in_tree k tree.
Proof.
  intros.
  induction kpl.
  Case "kpl = []".
    inversion H0.
    simpl in H6. apply ex_falso_quodlibet. omega.
  Case "kpl = a::kpl". destruct a. 
    simpl in H3.
    destruct kpl.
    rewrite ble_nat_symm in H3.
    rewrite <- beq_nat_refl in H3.
  admit.
  admit.
Admitted.

Theorem insert_works : forall {X: Type} {b: nat} (t t1: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> 
  ~appears_in_tree k t -> 
  insert k v t = t1 -> 
  appears_in_tree k t1.
Proof.
  intros.
  induction H.
  Case "leaf".
	unfold insert in H1.  unfold insert' in H1. simpl in H1. remember (insert_leaf b k v l) as il. 
	destruct il. destruct o.
	SCase "insert split".
	  assert ((l0, Some l1) = insert_leaf b k v l) by assumption.
	  apply insert_leaf_split_never_empty  in H4.
	  destruct l1. 
	    inversion H4. exfalso. apply H6. reflexivity.
	  destruct p.
	    
	  symmetry in Heqil. assert (insert_leaf b k v l = (l0, Some ((n,x)::l1))) by assumption.
	  apply insert_leaf_works in Heqil; try assumption.
	    rewrite <- H1. apply appears_in_split_node_appears_in_lists. destruct Heqil. 
	    apply insert_leaf_preserves_sort in H5; assumption; assumption.
	    apply insert_leaf_preserves_sort in H5; assumption; assumption.
	    simpl. reflexivity.
	    destruct Heqil. left. assumption.
	    inversion H6. right. do 3 destruct H6. inversion H7. inversion H6. rewrite H11. assumption.
	    unfold not. intro. apply H0. apply ait_leaf. apply H6.
	    assumption.
	SCase "insert_normal".
	  symmetry in Heqil. apply insert_leaf_normal in Heqil; try assumption. rewrite <- H1. 
	  apply ait_leaf; try assumption. unfold not. intro. unfold not in H0.
	  eapply appears_kvl_appears_leaf_tree in H4. apply H0. apply H4. 
	  apply insert_leaf_not_split_impl_space_left in Heqil. assumption.
	  unfold not. unfold not in H0. intros. apply H0. apply ait_leaf. assumption.
  Case "node". 
    unfold insert in H1.
    remember (insert' (height (bptNode b X kpl)) k v (bptNode b X kpl)).
    destruct p. destruct o.
    SCase "node overflow".
      destruct p.
      subst.
      admit.
    SCase "node normal".
      subst.
      symmetry in Heqp. apply insert'_normal in Heqp; try assumption.
      apply insert'_not_split_impl_space_left in Heqp; try assumption.
Admitted.
    





