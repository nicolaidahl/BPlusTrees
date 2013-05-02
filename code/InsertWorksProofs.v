Require Export BPlusTree.
Require Export HelperProofs.
Require Import SortingProofs.
Require Export HelperFunctions.
Require Import ValidBPlusTree.
Require Import AppearsInKVL.
  
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

Lemma appears_cons : forall (X: Type) (k k1: nat) (v1: X) (l: list (nat*X)),
  appears_in_kvl k ((k1, v1) :: l) -> 
  k <> k1 -> 
  appears_in_kvl k (l).
Proof.
  intros.
  inversion H.
  subst.
  apply ex_falso_quodlibet. omega.
  subst.
  apply H2.
Qed.

Lemma key_greater_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below (S kb) ) l ->
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

Lemma element_at_index_cons : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat*X)),
  kvl_sorted ((k1, v1) :: l) ->
  element_at_index b ((k1, v1) :: l) = Some (k2, v2) -> 
  (b = 0 /\ k1 = k2) \/ (b <> 0 /\ k1 < k2).
Proof.
  intros X.
  induction b.
  Case "b = 0".
    intros. left.
    simpl in H0. inversion H0.
    omega.
  Case "b = S b".
    intros. right.
    simpl in H0.
    destruct l.
    SCase "l = []".
      apply element_at_index_impl_appears in H0. inversion H0.
    SCase "l = p::l".
      destruct p.
      inversion H.
      apply blt_nat_true in H7.
      subst.
      apply element_at_index_impl_appears in H0.
      apply appears_in_kvl_app in H0.
      do 3 destruct H0.
      rewrite H0 in H.
      apply kvl_sorted_key_across_app in H.
      omega.
Qed.

Lemma element_at_index_b_elem_impl_pred_b: forall (X: Type) b (x: (nat * X)) l,
  b <> 0 ->
  element_at_index b (x :: l) = element_at_index (pred b) l.
Proof.
  induction b. 
    intros. admit. admit. (*split.
    unfold not in H. destruct H. reflexivity.
    intros. apply ex_falso_quodlibet. omega. 
    intros. split. intro.
    simpl. simpl in H0. assumption.
    intro. simpl in H0. assumption.*)
Admitted.



Lemma element_at_index_empty_none : forall (X: Type) b,
  @element_at_index X b [] = None.
Proof.
  intros. destruct b; reflexivity.
Qed.
  
Lemma element_at_index_one : forall (X: Type) b (k k1:nat) (v v1: X),
  element_at_index b [(k, v)] = Some (k1, v1) -> k = k1.
Proof. 
  intros. induction b. compute in H. inversion H. reflexivity.
  simpl in H. rewrite element_at_index_empty_none in H. inversion H.
Qed.

(*Lemma element_at_index_pred_b_implies_left_below_S_b : 
  forall (X: Type) (b k1: nat) (v1: X) (l l1 l2: list (nat*X)),
  b <> 0 ->
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index (pred b) l = Some (k1, v1) ->
  all_keys X (below (S k1)) l1. 
Proof.
  induction b; intros.
  Case "b = 0".
    rewrite length_0_impl_nil. apply ak_empty. assumption.
  Case "b = S b".
    simpl in H2. destruct l. 
    SCase "l = []".
      apply element_at_index_impl_appears in H3. inversion H3.
    SCase "l = p :: l".
      destruct l1.
      SSCase "l1 = []". 
        apply ak_empty.
      SSCase "l1 = p0 :: l1".
        simpl in H1. simpl in H2. inversion H2. inversion H1. rewrite <- H6. destruct p. 
        apply ak_next. apply IHb with (v1:=v1)(l:=l)(l2:=l2); try assumption.
        admit.
        apply list_tail_is_sorted in H0. assumption.
        eapply element_at_index_b_elem_impl_pred_b. admit.
        apply H3.
        SSSCase "S k1 > n".
          unfold below. apply blt_nat_true. simpl in H3. apply element_at_index_impl_appears in H3.
          apply appears_in_kvl_app in H3. do 3 destruct H3. destruct witness. inversion H3. omega.
          inversion H3. rewrite H3 in H0. rewrite <- H8 in H0. 
          apply kvl_sorted_key_across_app in H0. omega.
Qed.*)

(* a try with induction on kvl_sorted 
  
  intros. generalize dependent l1. generalize dependent l2.
  induction H0; intros. 
  Case "kvl_sorted_0".
    apply element_at_index_impl_appears in H3. inversion H3.
  Case "kvl_sorted_1".
    destruct l1. apply ak_empty. 
    inversion H1. symmetry in H5. apply app_eq_nil in H5. destruct H5. rewrite H0.
    apply ak_next. apply ak_empty. unfold below. apply blt_nat_true.
    destruct b. unfold not in H. destruct H. reflexivity.
    simpl in H3. apply element_at_index_one in H3. omega.
  Case "kvl_sorted_cons".
    destruct l1. apply ak_empty.
    
    *)
        

Lemma element_at_index_b_implies_left_below_b : forall (X: Type) (b k1: nat) (v1: X) (l l1 l2: list (nat*X)),
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index b l = Some (k1, v1) ->
  all_keys X (below k1) l1. 
Proof.
  intros.
  generalize dependent l. generalize dependent l1.
  induction b.
  Case "b = 0".
    intros.
    apply length_0_impl_nil in H1.
    subst.
    apply ak_empty.
  Case "b = S b".
    intros.
    destruct l.
    SCase "l = []".
      apply element_at_index_impl_appears in H2.
      inversion H2.
    SCase "l = h :: t".
      simpl in H2.
      destruct l1.
      SSCase "l1 = []".
        apply ak_empty.
      SSCase "l1 = h :: t".
        rewrite <- app_comm_cons in H0.
        inversion H0.
        rewrite <- H4.
        destruct p.
        apply ak_next.
        SSSCase "rest of list below".
          apply IHb with (l := l); try assumption.
            simpl in H1. inversion H1. reflexivity.
            apply list_tail_is_sorted in H. assumption.
        SSSCase "below k1 n".
          unfold below. rewrite blt_nat_true.
          destruct l.
            SSSSCase "l = []".
              apply element_at_index_impl_appears in H2. inversion H2.
            SSSSCase "l = h :: t".
              destruct p.
		      inversion H.
		      destruct b.
		      SSSSSCase "b = 0".
		        simpl in H2.
		        inversion H2.
		        apply blt_nat_true in H11. subst.
		        assumption.
		      SSSSSCase "b = S b".
		        apply element_at_index_cons in H2.
			    inversion H2.
			    inversion H12.
			    inversion H13.
			    inversion H12.
		        apply blt_nat_true in H11. omega.
		        apply list_tail_is_sorted in H.
		        assumption.
Qed.

Lemma all_keys_elim_cons : forall (X: Type) (k1 k2: nat) (v1 v2: X) (l: list (nat*X)),
  above k1 k2 -> all_keys X (above k1) ((k1, v1) :: l) -> all_keys X (above k1) ((k1, v1) :: (k2, v2) :: l).
Proof.
  intros.
  inversion H0.
  inversion H3. 
  repeat constructor; assumption.
  repeat constructor; assumption.
Qed.

Lemma sorted_all_keys_above_cons : forall (X: Type) (l: list (nat*X)) (k: nat) (v1: X), 
  kvl_sorted ((k, v1)::l) -> all_keys X (above k) ((k, v1)::l).
Proof.
  induction l.
  Case "l = []".
    intros.
    apply ak_next. apply ak_empty.
    unfold above. apply ble_nat_symm.
  Case "l = a::l".
    intros.
    destruct a.
    inversion H. subst.
    apply blt_nat_true in H6.
    
    (* Remove a from list in proof obligation *)
    apply all_keys_elim_cons.
    unfold above. apply ble_nat_true. omega.
    
    (* Now apply induction hypothesis *)
    apply IHl.
    replace ((k,v1)::(n,x)::l) with ([(k,v1)]++[(n,x)]++l) in H by reflexivity.
    apply kvl_sorted_elim_list in H.
    simpl in H. apply H.
Qed.

Lemma element_at_index_b_implies_right_above_b : forall (X: Type) (l l1 l2: list (nat*X)) (b k1: nat) (v1: X),
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index b l = Some (k1, v1) ->
  all_keys X (above k1) l2. 
Proof.
  induction l.
  Case "l = []".
    intros.
    symmetry in H0. apply app_eq_nil in H0. inversion H0.
    subst. simpl in *. inversion H2.
  Case "l = a::l".
    intros. destruct a.
    destruct b.
    SCase "b = 0".
      apply length_0_impl_nil in H1. subst.
      simpl in H0. subst.
      simpl in H2. inversion H2. subst.
      apply sorted_all_keys_above_cons.
      apply H.
    SCase "b = S b".
      simpl in H2.
      destruct l1.
      SSCase "l1 = []".
        simpl in H1. inversion H1.
      SSCase "l1 = p::l1".
        rewrite <- app_comm_cons in H0.
        inversion H0.
        simpl in H1. inversion H1.
        eapply IHl.
          apply list_tail_is_sorted in H. apply H.
          apply H5.
          apply H6.
          apply H2.
Qed.

Lemma element_unchanged_by_inserting_greater_key : forall (X: Type) (b k1 k2 k3: nat) (v1 v2 v3: X) (l: list (nat*X)),
  kvl_sorted ((k1, v2)::l) ->
  element_at_index b ((k1, v1) :: l) = Some (k2, v2) ->
  k3 > k2 ->
  element_at_index b ((k1, v1) :: insert_into_list k3 v3 l) = Some (k2, v2).
Proof.
  induction b.
  Case "b = 0".
    intros.
    simpl. simpl in H. inversion H0. reflexivity.
  Case "b = S b".
    intros.
    simpl.
    destruct l.
    simpl in H0. apply element_at_index_impl_appears in H0. inversion H0.
    destruct p.
    assert (kvl_sorted(insert_into_list k3 v3 ((n, x) :: l))).
      apply insert_preserves_sort. apply list_tail_is_sorted in H.
      apply H.
    simpl. simpl in H2.
    remember (ble_nat k3 n) as k3len.
    destruct k3len; symmetry in Heqk3len; [apply ble_nat_true in Heqk3len|apply ble_nat_false in Heqk3len].
    SCase "k3 <= n".
      remember (beq_nat k3 n) as k3eqn.
      destruct k3eqn; symmetry in Heqk3eqn; [apply beq_nat_true_iff in Heqk3eqn|apply beq_nat_false_iff in Heqk3eqn].
      SSCase "k3 = n".
      simpl in H0.
        destruct b.
        simpl in H0. inversion H0.
        subst.
        apply n_lt_n_inversion with (n := k2). apply H1.
        simpl. simpl in H0. apply H0.
      SSCase "k3 < n".
        simpl in H0.
        destruct b.
        SSSCase "b = 0".
          simpl in H0. inversion H0. subst.
          inversion H2.
          apply blt_nat_true in H9.
          apply ex_falso_quodlibet. omega.
        SSSCase "b = S b".
          apply element_at_index_cons in H0. destruct H0.
          inversion H0. inversion H3.
          inversion H0. subst.
          apply ex_falso_quodlibet. omega.
          apply list_tail_is_sorted in H. apply H.	
    SCase "k3 > n".
      simpl in H0.
      apply IHb.
      apply list_tail_is_sorted in H. 
      apply sort_ignores_value with (v1 := x) (v2 := v2) in H.
      apply H.
      apply H0.
      apply H1.
Qed.

Lemma element_changed_by_inserting_smaller_key : forall (X: Type) (b k1 k2 k3: nat) (v1 v2 v3: X) (l: list (nat*X)),
  kvl_sorted ((k1, v2)::l) ->
  element_at_index (pred b) ((k1, v1) :: l) = Some (k2, v2) ->
  k3 < k2 ->
  element_at_index b ((k1, v1) :: insert_into_list k3 v3 l) = Some (k2, v2).
Proof.
  admit.
Admitted.

Theorem split_insert_right : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index (pred b) leaf = Some (kb, vb) -> 
  kb <= k -> length leaf = mult b 2 -> 
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
           (*simpl in H2.
           apply split_list_left_length in H5.
           apply element_unchanged_by_inserting_greater_key with (k3 := k) (v3 := v) in H2; try assumption.
           simpl in H4.
           inversion H4. clear H4.
           apply element_at_index_pred_b_implies_left_below_S_b with (l1 := left) (l2 := kvl) in H2; try assumption.
           apply key_greater_than_all_keys_does_not_appear with (k:=k) in H2; try assumption.
           We've found our inversion - k both appears and does not appear in left
           apply ex_falso_quodlibet. apply H2. apply H8.
           
           (Now we just need to prove all of the assumptions
           symmetry in H7. apply split_preserves_sort in H7; try assumption.
           inversion H7. assumption.
           
           apply insert_preserves_sort_cons; assumption. 
           apply insert_preserves_sort_cons; assumption.
           apply sort_ignores_value with (v1 := x) (v2 := vb). apply H0.
           simpl in H4.
           rewrite <- insert_new_into_list_increases_length with (k := k) (v := v) (l := leaf) in H4.
           simpl. rewrite H4.  omega.
           apply list_tail_is_sorted in H0. assumption.
           unfold not. intro. apply H1. apply ai_later. assumption.
           reflexivity.*)
           admit.
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

             apply element_changed_by_inserting_smaller_key with (k3:=k) (v3:= v) in H2.
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
             
             apply sort_ignores_value with (v1:=x)(v2:=vb) in H0. apply H0.
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


Theorem split_insert_normal : forall {X: Type} {b: nat} (leaf left: list (nat * X)) (k: nat) (v: X),
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

Lemma blargh : forall (X: Type) (x1 x2: X) (l: list X),
  x1::l <> [] -> x1::x2::l <> [].
Proof.
  intros. unfold not. intro. inversion H0.
Qed.

Lemma list_of_length_b_implies_element_at_b : forall (X: Type) (b: nat) (kvl: list (nat* X)),
  b <= length kvl -> 
  (kvl = [] /\ element_at_index (pred b) kvl = None) 
    \/ 
  (kvl <> [] /\ exists k, exists v, element_at_index (pred b) kvl = Some(k, v)).
Proof.
  intros. 
  
  (*
   * We can try an induction on kvl.
  generalize dependent b.
  induction kvl.
  Case "kvl = []".
    intros.
    left. split. reflexivity. rewrite element_at_index_empty_none. reflexivity.
  Case "kvl = a::kvl".
    intros.
    destruct a.
    destruct b.
    SCase "b = 0".
      right.
      split. 
      unfold not. intro. inversion H0.
      simpl. exists n. exists x. reflexivity.
    SCase "b = S b".
      simpl.
      * And now we have b instead of pred b *)
      
  (*
   * Or we can try on b *)
  induction b.
  Case "b = 0".
    intros. destruct kvl.
    left.
      split. reflexivity. rewrite element_at_index_empty_none. reflexivity.
    right.
    split.
      unfold not. intro. inversion H0.
      destruct p. simpl. exists n. exists x. reflexivity.
  Case "b = S b".
    intros. destruct kvl.
    left.
      split. reflexivity. rewrite element_at_index_empty_none. reflexivity.
    simpl.
    (* And again we have b instead of pred b *)
    
    destruct b.
      SCase "b = 0".
      right.
      split.
        unfold not. intro. inversion H0.
        simpl. destruct p. exists n. exists x. reflexivity.
      SCase "b = S b".
        simpl. simpl in IHb.
        (* And here we have a miss-match between p::kvl and kvl *)    
  admit.
Admitted.

Theorem insert_leaf_works : forall {X: Type} {b: nat} (k: nat) (v: X) (leaf left right: list (nat * X)),
  b <> 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> 
  length leaf <= mult b 2 ->
  exists rightOption: option (list (nat * X)), insert_leaf b k v leaf = (left, rightOption) ->
  appears_in_kvl k left \/ rightOption = Some(right) /\ appears_in_kvl k right.
Proof.
  intros.
  remember (blt_nat (length leaf) (b * 2)) as blt_length_b.
  destruct blt_length_b; symmetry in Heqblt_length_b; [apply blt_nat_true in Heqblt_length_b | apply blt_nat_false in Heqblt_length_b].
  Case "less".
    exists None.
    left.
    eapply split_insert_normal. 
      apply H.
      apply H0.
      apply H1.
      apply Heqblt_length_b.
      apply H3.
  Case "equal".
    assert (length leaf = b * 2) by omega.
    assert (b <= length leaf) by omega.
    apply list_of_length_b_implies_element_at_b in H4.
    inversion H4.
      inversion H5. rewrite H6 in H3. simpl in H3. assert (b=0) by omega. 
      apply ex_falso_quodlibet. omega.
    inversion H5.
    do 2 destruct H7. clear H4. clear H5. clear H6.
    remember (ble_nat witness k) as ble_kb_k.
    destruct ble_kb_k; symmetry in Heqble_kb_k; [apply ble_nat_true in Heqble_kb_k | apply ble_nat_false in Heqble_kb_k].
    SCase "right".
      exists (Some right).
      right.
      split.
      SSCase "right = right".
        reflexivity.
      SSCase "appears in".
        eapply split_insert_right.
          apply H.
          apply H0.
          apply H1.
          apply H7.
          apply Heqble_kb_k.
          apply H3.
          apply H4.
    SCase "split left".
      exists (Some right).
      left.
      eapply split_insert_left.
        apply H.
        apply H0.
        apply H1.
        apply H7.
        omega.
        apply H3.
        apply H4.
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
  length kvl <= mult b 2 -> insert_leaf (S b) n v ((n, x) :: kvl) = ((n, v) :: kvl, None).
Proof.
  intros.
  unfold insert_leaf. unfold insert_into_list.
  rewrite ble_nat_symm. rewrite <- beq_nat_refl.
  simpl.
  remember (ble_nat (length kvl) (S (b * 2))) as lb2.
  destruct lb2.
  reflexivity.
  symmetry in Heqlb2. apply ble_nat_false in Heqlb2.
  unfold not in Heqlb2.
  apply ex_falso_quodlibet.
  apply Heqlb2. apply le_S. apply H.
Qed.    

Lemma lt_S : forall (n m: nat),
  n < m <-> S n < S m.
Proof.
Admitted.

Theorem insert_leaf_normal : forall (X: Type) (b: nat) (k: nat) (v: X) (kvl: list (nat * X)),
  b <> 0 -> kvl_sorted kvl -> S (length(kvl)) < mult b 2-> 
  insert_leaf b k v kvl = (insert_into_list k v kvl, None).
Proof.
  intros. 
  destruct b. apply ex_falso_quodlibet. apply H. reflexivity. clear H.
  induction kvl. 
  Case "kvl = []".
    unfold insert_leaf.
    simpl. reflexivity. 
  Case "kvl = a::kvl".
    destruct a. simpl. remember (ble_nat k n) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n".
      remember (beq_nat k n) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n". subst. 
        apply insert_leaf_shaddow.
        simpl in H1. apply lt_S in H1. apply lt_S in H1.
        apply lt_le_weak in H1. apply H1.
      SSCase "k <> n".
        admit.  
    SCase "k > n". 
      admit.
Admitted.

Theorem insert_leaf_split : forall (X: Type) (b: nat) (k: nat) (v: X) (kvl kvl1 kvl2: list (nat * X)),
  kvl_sorted kvl -> length(kvl) = mult b 2 -> 
  (kvl1, kvl2) = split_list b (insert_into_list k v kvl1) -> 
  insert_leaf b k v kvl = (kvl1, Some kvl2).
Proof.
  admit.
Admitted.

Theorem insert_works : forall (b: nat) (X: Type) (t: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> search k (insert k v t) = Some v.
Proof.
  intros.
  induction H.
  Case "leaf".
    unfold insert. remember (insert' k v (bptLeaf b X l)) as insert'. destruct insert'.
  admit.
  admit.
Admitted.
    
