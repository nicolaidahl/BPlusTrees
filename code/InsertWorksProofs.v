Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.
Require Export ValidBPlusTree.
Require Export AppearsInKVL.
Require Export AppearsInTree.
Require Export ElementAtIndexProofs.
Require Export SplitCutList.
  
Lemma split_never_returns_empty_none : forall (X: Type) (b: nat) (leaf: list (nat * X)) (k: nat) (v: X),
  b <> 0 -> insert_leaf b k v leaf = ([], None) -> False. 
Proof.
  intros. 
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
  
  induction leaf. 
  Case "leaf = []". 
    unfold insert_leaf in H0. simpl in H0. inversion H0.
  Case "leaf = a::leaf".
    destruct a. 
    unfold insert_leaf in H0. simpl in H0.
    remember (ble_nat k n) as klen. 
      destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
      SCase "k <= n". remember (beq_nat k n) as keqn. 
        destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
        SSCase "k = n".
          remember (ble_nat (length ((k, v) :: leaf)) (S (S (b * 2)))) as too_long. 
          destruct too_long.  inversion H0. 
          remember (split_list (S b) ((k, v) :: leaf)) as rtn.
          destruct rtn. inversion H0.
        SSCase "k <> n".
          remember (ble_nat (length ((k, v) :: (n,x) :: leaf)) (S (S (b * 2)))) as too_long. 
          destruct too_long. inversion H0. 
          remember (split_list (S b) ((k, v) :: (n,x) :: leaf)) as rtn.
          destruct rtn. inversion H0.
      SCase "k > n".
        remember (ble_nat (length ((n, x) :: insert_into_list k v leaf)) (S (S (b * 2)))) as too_long. 
        destruct too_long. inversion H0. 
        remember (split_list (S b) ((n, x) :: insert_into_list k v leaf)) as rtn.
        destruct rtn. inversion H0.
Qed.

Lemma insert_into_list_increases_length : forall (X: Type) (l: list (nat * X)) (k n: nat) (v: X),
  kvl_sorted l -> length l <= n -> length (insert_into_list k v l) <= S n.
Proof.
  intros. generalize dependent l. induction n; intros.
  simpl.
  Case "n = 0".
    apply length_gt_0_impl_nil in H0. subst. simpl. omega.
  Case "n = S n".
    destruct l. simpl. omega.
    destruct p.
    simpl. remember (ble_nat k n0) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n0".
      remember (beq_nat k n0) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn];
      simpl; simpl in H0; omega.
    SCase "k > n0".
      simpl. apply le_n_S. apply IHn.
      apply list_tail_is_sorted in H. apply H.
      simpl in H0. inversion H0; omega.
Qed.

Lemma insert_new_into_list_increases_length : forall (X: Type) (l: list (nat * X)) (k n: nat) (v: X),
  kvl_sorted l -> ~(appears_in_kvl k l ) -> length l = n -> length (insert_into_list k v l) = S n.
Proof.
  intros.
  generalize dependent l. induction n; intros.
  Case "n = 0".
    apply length_0_impl_nil in H1. subst. simpl. omega.
  Case "n = S n".
    destruct l. simpl in H1.  inversion H1.
    destruct p.
    simpl. remember (ble_nat k n0) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n0".
      remember (beq_nat k n0) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n0".
        subst.
        apply ex_falso_quodlibet.
        apply H0. apply ai_here.
      SSCase "k < n0".
        simpl. simpl in H1. omega.
    SCase "k > n0".
      simpl. apply eq_remove_S.
      apply IHn.
      apply list_tail_is_sorted in H.
      apply H.
      unfold not.
      intros.
      apply H0.
      apply ai_later. apply H2.
      simpl in H1. omega.
Qed.

Lemma insert_new_into_list_increases_length_lt : forall (X: Type) (l: list (nat * X)) (k n: nat) (v: X),
  kvl_sorted l -> ~(appears_in_kvl k l ) -> length l < n -> length (insert_into_list k v l) <= n.
Proof.
  intros.
  generalize dependent l. induction n; intros.
  Case "n = 0".
    apply ex_falso_quodlibet. omega.
  Case "n = S n".
    destruct l. simpl. omega.
    destruct p.
    simpl. remember (ble_nat k n0) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n0".
      remember (beq_nat k n0) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n0".
        subst. simpl.
        apply ex_falso_quodlibet.
        apply H0. apply ai_here.
      SSCase "k < n0".
        simpl. simpl in H1. omega.
    SCase "k > n0".
      simpl. apply le_n_S.
      apply IHn.
      apply list_tail_is_sorted in H.
      apply H.
      unfold not.
      intros.
      apply H0.
      apply ai_later. apply H2.
      simpl in H1. omega.
Qed.


Lemma insert_leaf_cons_eq : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2, v2)::l) -> k1 = k2 -> length((k2,v2)::l) <= mult b 2 -> insert_leaf b k1 v1 ((k2, v2) :: l) = ((k1,v1)::l, None).
Proof.
  intros. 
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity. subst.
  unfold insert_leaf. simpl. rewrite ble_nat_symm. rewrite <- beq_nat_refl.
  remember (ble_nat (length ((k2, v1) :: l)) (S (S (b * 2)))) as too_long.
  destruct too_long.
  reflexivity.
  symmetry in Heqtoo_long. apply ble_nat_false in Heqtoo_long.
  apply ex_falso_quodlibet.
  apply Heqtoo_long.
  simpl.
  simpl in H2.
  omega.
Qed.

Lemma insert_leaf_cons_lt : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 < k2 -> length((k2,v2)::l) < mult b 2 -> insert_leaf b k1 v1 ((k2, v2) :: l) = ((k1,v1)::(k2,v2)::l, None).
Proof.
  intros.
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
  unfold insert_leaf. simpl. 
  remember (ble_nat k1 k2) as k1lek2.
  destruct k1lek2; symmetry in Heqk1lek2; [apply ble_nat_true in Heqk1lek2|apply ble_nat_false in Heqk1lek2].
  Case "k1 <= k2".
    remember (beq_nat k1 k2) as k1eqk2.
    destruct k1eqk2; symmetry in Heqk1eqk2; [apply beq_nat_true_iff in Heqk1eqk2|apply beq_nat_false_iff in Heqk1eqk2].
    SCase "k1 = k2".
      subst.
      apply n_lt_n_inversion with (n := k2). assumption.
    SCase "k1 <> k2".
      simpl. assert (ble_nat (length l) (b * 2) = true). apply ble_nat_true. simpl in H2. omega.
      rewrite H3. reflexivity.
  Case "k1 > k2".
    apply ex_falso_quodlibet. apply Heqk1lek2. omega.
Qed.

Lemma insert_leaf_cons_lt_overflow : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2, v2)::l) -> k1 < k2 -> length((k2,v2)::l) = mult b 2 -> insert_leaf b k1 v1 ((k2, v2) :: l) = (let (fst, snd) := split_list b ((k1, v1) :: (k2, v2) :: l) in (fst, Some snd)).
Proof.  
  intros.
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
  unfold insert_leaf. simpl.
  remember (ble_nat k1 k2) as k1lek2.
  destruct k1lek2; symmetry in Heqk1lek2; [apply ble_nat_true in Heqk1lek2|apply ble_nat_false in Heqk1lek2].
  Case "k1 <= k2".
    remember (beq_nat k1 k2) as k1eqk2.
    destruct k1eqk2; symmetry in Heqk1eqk2; [apply beq_nat_true_iff in Heqk1eqk2|apply beq_nat_false_iff in Heqk1eqk2].
    SCase "k1 = k2".
      subst.
      apply n_lt_n_inversion with (n := k2). assumption.
    SCase "k1 <> k2".
      simpl. simpl in H2. inversion H2. rewrite H4. 
      remember (ble_nat (S (b * 2)) (b * 2)) as too_long.
      destruct too_long.
      symmetry in Heqtoo_long. apply ble_nat_true in Heqtoo_long. 
      apply Sn_le_n_inversion with (n := b*2). assumption.
      reflexivity.
  Case "k1 > k2".
    apply ex_falso_quodlibet. apply Heqk1lek2. omega.
Qed.

Lemma insert_leaf_cons_gt : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 > k2 -> length((k2,v2)::l) < mult b 2 -> insert_leaf b k1 v1 ((k2, v2) :: l) = ((k2,v2):: insert_into_list k1 v1 l, None).
Proof.
  intros.
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
  unfold insert_leaf. simpl.
  remember (ble_nat k1 k2) as k1lek2.
  destruct k1lek2; symmetry in Heqk1lek2; [apply ble_nat_true in Heqk1lek2|apply ble_nat_false in Heqk1lek2].
  Case "k1 <= k2".
    apply ex_falso_quodlibet. omega.
  Case "k1 > k2".
    simpl.
    remember (ble_nat (length (insert_into_list k1 v1 l)) (S (b * 2))) as too_long.
    destruct too_long;
    symmetry in Heqtoo_long; [apply ble_nat_true in Heqtoo_long|apply ble_nat_false in Heqtoo_long].
    SCase "not too long".
      reflexivity.
    SCase "too long".
      apply ex_falso_quodlibet.
      apply Heqtoo_long.
      apply insert_into_list_increases_length.
      apply list_tail_is_sorted in H0.
      apply H0.
      simpl in H2.
      omega.
Qed.

Lemma insert_leaf_cons_gt_overflow : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 > k2 -> ~(appears_in_kvl k1 l) -> length((k2,v2)::l) = mult b 2 -> 
  insert_leaf b k1 v1 ((k2, v2) :: l) = (let (fst, snd) := split_list b ((k2, v2) :: insert_into_list k1 v1 l) in (fst, Some snd)).
Proof.
  intros.
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity.
  unfold insert_leaf. simpl.
  remember (ble_nat k1 k2) as k1lek2.
  destruct k1lek2; symmetry in Heqk1lek2; [apply ble_nat_true in Heqk1lek2|apply ble_nat_false in Heqk1lek2].
  Case "k1 <= k2".
    apply ex_falso_quodlibet. omega.
  Case "k1 > k2".
    simpl.
    remember (ble_nat (length (insert_into_list k1 v1 l)) (S (b * 2))) as too_long.
    destruct too_long;
    symmetry in Heqtoo_long; [apply ble_nat_true in Heqtoo_long|apply ble_nat_false in Heqtoo_long].
    SCase "not too long".
      simpl in H3.
      inversion H3.
      apply list_tail_is_sorted in H0.
      apply insert_new_into_list_increases_length with (k := k1) (v := v1) (n := S (b*2)) in H0.
      rewrite H0 in Heqtoo_long.
      apply Sn_le_n_inversion with (n := S(b*2)). assumption.
      apply H2. apply H5.
    SCase "too long".
      reflexivity.
Qed.

Theorem insert_into_list_appears : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  appears_in_kvl k (insert_into_list k v l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. apply ai_here.
  Case "l = a::l".
    destruct a. simpl. 
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        apply ai_here.
      SSCase "k <> n".
      apply ai_here.
    SCase "k > n".
      apply ai_later. apply IHl.
Qed.



Lemma key_greater_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below kb) l ->
  k > kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst. 
  inversion H3. apply blt_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.

Lemma key_greater_than_all_keys_does_not_appear_ble : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below_equal kb) l ->
  k > kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst. 
  inversion H3. apply ble_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.

Lemma key_smaller_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (above kb) l ->
  k < kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  subst. inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst.
  inversion H3. apply ble_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.








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

Theorem insert_into_list_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> search_leaf k (insert_into_list k v l) = Some v. 
Proof.
  intros. induction l.
  Case "l = []". simpl. rewrite <- beq_nat_refl. reflexivity.
  Case "l = a::l".  simpl. destruct a. remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n". simpl. rewrite <- beq_nat_refl. reflexivity.
      SSCase "k != n". simpl. rewrite <- beq_nat_refl. reflexivity.
    SCase "k > n". simpl. remember (beq_nat n k) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        subst. unfold not in Heqklen. apply ex_falso_quodlibet. apply Heqklen. omega.
      SSCase "k != n". apply IHl.
      apply list_tail_is_sorted in H. apply H.
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

Theorem appears_kvl_appears_leaf_tree: forall {X: Type} (b: nat) k l,
  appears_in_kvl k l -> appears_in_tree k (bptLeaf b X l).
Proof.
  intros. induction H. apply ait_leaf. apply ai_here. apply ait_leaf.
  eapply appears_in_super_set_appears. reflexivity. apply H.
Qed.

Lemma insert_not_split_impl_space_left: forall {X: Type} (b: nat) k (v:X) l l',
  ~ appears_in_kvl k l ->
  insert_leaf b k v l = (l', None) -> length l < b * 2.
Proof.
  intros. unfold insert_leaf in H. remember (ble_nat (length (insert_into_list k v l)) (b * 2)) as blelen.
  destruct blelen. Admitted.



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
    apply ait_node_later. apply ait_node_one. apply ait_leaf. assumption. 
    SCase "n <=".
      inversion H0. destruct right. inversion H3. destruct p. inversion H3. subst. remember (beq_nat n k).
      destruct b0. symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. omega.
      apply appears_cons in H1. apply appears_in_kvl_app in H1. do 3 destruct H1. subst.
      apply kvl_sorted_app with (l1:=left) in H. inversion H. 
      apply kvl_sorted_key_across_app in H2.  omega. symmetry in Heqb0. 
      apply beq_nat_false in Heqb0. omega.
    SCase "< n".
    inversion H0. destruct right. inversion H3. destruct p. inversion H3. subst.
    remember (beq_nat n k).
    destruct b0. symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. omega.
    apply appears_cons in H1. apply appears_in_kvl_app in H1. do 3 destruct H1. subst.
    apply kvl_sorted_app with (l1:=left) in H. inversion H. 
    apply kvl_sorted_key_across_app in H2. omega. symmetry in Heqb0. 
    apply beq_nat_false in Heqb0. omega.
Qed.


Lemma key_at_index_0none_impl_empty: forall (X: Type) l,
  @key_at_index X 0 l = None -> l = [].
Proof. 
  intros. unfold key_at_index in H. destruct l. reflexivity. destruct p. inversion H.
Qed.

Lemma insert_leaf_preserves_sort: forall (X: Type) b k (v:X) l l1 l2,
  kvl_sorted l ->
  insert_leaf b k v l = (l1, Some l2) ->
  kvl_sorted(l1 ++ l2).
Proof. Admitted.

Theorem insert_works : forall {X: Type} {b: nat} (t t1: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> 
  ~appears_in_tree k t -> 
  insert k v t = t1 -> 
  appears_in_tree k t1.
Proof.
  intros.
  induction H.
  Case "leaf".
	unfold insert in H1.  unfold insert' in H1. remember (insert_leaf b k v l) as il. 
	destruct il. destruct o.
	SCase "insert split".
	  symmetry in Heqil. assert (insert_leaf b k v l = (l0, Some l1)).  assumption.
	  apply insert_leaf_works in Heqil; try assumption.
	  remember (key_at_index 0 l1) as kat. destruct kat.
	  SSCase "kat = (l0, Some l1)".
	    rewrite <- H1. apply appears_in_split_node_appears_in_lists. destruct Heqil. 
	    apply insert_leaf_preserves_sort in H4; assumption; assumption.
	    apply insert_leaf_preserves_sort in H4; assumption; assumption.
	    symmetry in Heqkat. assumption.
	    destruct Heqil. left. assumption.
	    inversion H5. right. do 3 destruct H5. inversion H6. inversion H5. assumption.
	    rewrite <- H1. apply ait_leaf. destruct Heqil. assumption.
	    symmetry in H4. apply insert_leaf_split_never_empty in H4. destruct H4.
	    symmetry in Heqkat. apply key_at_index_0none_impl_empty in Heqkat. unfold not in H6.
	    apply H6 in Heqkat. inversion Heqkat. assumption.
	    unfold not. intros. unfold not in H0. apply H0. apply ait_leaf.  assumption.
	SCase "insert_normal".
	  symmetry in Heqil. apply insert_leaf_normal in Heqil; try assumption. rewrite <- H1. 
	  apply ait_leaf; try assumption. unfold not. intro. unfold not in H0.
	  eapply appears_kvl_appears_leaf_tree in H4. apply H0. apply H4. 
	  apply insert_not_split_impl_space_left in Heqil. assumption.
	
  Case "node". 
    admit.
	 
Admitted.
    

  
  
  
  
  
  
  
  

