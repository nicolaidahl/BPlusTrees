Require Export BPlusTree.
Require Export HelperProofs.
Require Export ValidBPlusTree.

Example kvl_sorted_empty : @kvl_sorted nat [].
Proof. apply kvl_sorted_0. Qed.
Example kvl_sorted_single : kvl_sorted [(1, 1)].
Proof. apply kvl_sorted_1. Qed.
Example kvl_sorted_two : kvl_sorted [(1, 1), (2, 2)].
Proof. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. Qed.
Example kvl_sorted_two_WRONG : kvl_sorted [(2, 2), (1, 1)] -> False.
Proof. unfold not. intro. inversion H. inversion H6. Qed.

Lemma sort_ignores_value : forall (X: Type) (k: nat) (v1 v2: X) (l: list (nat * X)),
  kvl_sorted ((k,v1)::l) -> kvl_sorted((k, v2)::l).
Proof.
  intros. inversion H. apply kvl_sorted_1.
  apply kvl_sorted_cons. apply H2. apply H4.
Qed.

Lemma list_tail_is_sorted : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted ((k,v)::l) -> kvl_sorted l.
Proof.
  intros.
  inversion H. apply kvl_sorted_0. apply H2.
Qed.

Lemma list_head_is_sorted : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted (l++[(k,v)]) -> kvl_sorted l.
Proof.
  intros. induction l.
  Case "l = []".
    apply kvl_sorted_0.
  Case "l = a::l".
    destruct a.
    destruct l. 
    SCase "l = []".
      apply kvl_sorted_1.
    SCase "l = a::p::l".
      destruct p.
      repeat rewrite <- app_comm_cons in H.
      inversion H. apply kvl_sorted_cons. apply IHl.
      apply list_tail_is_sorted in H. apply H.
      apply H6.
Qed.

Lemma kvl_sorted_app : forall (X: Type) (l1 l2: list (nat * X)),
  kvl_sorted (l1++l2) -> kvl_sorted l1 /\ kvl_sorted l2.
Proof.
  intros.
  split; intros. 
    SCase "kvl_sorted l1".
      induction l1.
      SSCase "l1 = []".
        apply kvl_sorted_0.
      SSCase "l1 = a::l1".
        rewrite <- app_comm_cons in H.
        destruct l1;  
        destruct a. apply kvl_sorted_1.
        destruct p. inversion H. subst.
        apply kvl_sorted_cons. apply IHl1.
        apply list_tail_is_sorted in H. apply H.
        apply H6.
    SCase "kvl_sorted l2".
      induction l1.
        simpl in H. apply H.
        apply IHl1.
        rewrite <- app_comm_cons in H.
        destruct a.
        apply list_tail_is_sorted in H. apply H.
    
Qed.

Lemma kvl_sorted_key_across_app : forall (X: Type) (l1 l2: list (nat * X)) (k1 k2: nat) (v1 v2: X),
  kvl_sorted((k1, v1)::l1 ++ (k2, v2)::l2) -> k1 < k2.
intros.
  induction l1.
  Case "l1 = []".
    simpl in H.
    inversion H. subst.
    apply blt_nat_true in H6. apply H6.
  Case "l1 = a::l1".
    apply IHl1. destruct l1.
    SCase "l1 = [a]".
      simpl in H. destruct a. simpl.
      inversion H. inversion H2. subst.
      apply blt_nat_true in H6.
      apply blt_nat_true in H13.
      apply kvl_sorted_cons. apply H9.
      apply blt_nat_true. omega.
    SCase "l1 = p::a::l1".
      repeat rewrite <- app_comm_cons in H.
      destruct p.
      rewrite <- app_comm_cons.
      inversion H. inversion H2. subst.
      apply blt_nat_true in H5.
      apply blt_nat_true in H12.
      apply kvl_sorted_cons. apply H8.
      apply blt_nat_true.
      omega.
Qed.

Lemma kvl_sorted_elim_list : forall (X: Type) (l1 l2 l3: list (nat * X)),
  kvl_sorted(l1++l2++l3) -> kvl_sorted(l1++l3).
Proof.
  intros. 
  induction l1.
  Case "l1 = []".
    simpl. simpl in H. apply kvl_sorted_app in H. inversion H.
    apply H1.
  Case "l1 = a::l1".
    destruct l1.
    SCase "l1 = [a]".
      simpl. simpl in H. simpl in IHl1. destruct l3. destruct a. apply kvl_sorted_1.
      destruct a. destruct p. apply kvl_sorted_cons.
      apply IHl1. apply list_tail_is_sorted in H. apply H.
      apply kvl_sorted_key_across_app in H.  apply blt_nat_true.  apply H. 
    SCase "l1 = a::p::l1".
      destruct a. destruct p. repeat rewrite <- app_comm_cons. 
      apply kvl_sorted_cons. apply IHl1.
      repeat rewrite <- app_comm_cons in H. apply list_tail_is_sorted in H.
      apply H.
      inversion H. apply H6.
Qed. 

Lemma kvl_sorted_elim_cons : forall (X: Type) (l1 l2: list (nat * X)) (k: nat) (v: X),
  kvl_sorted (l1++((k, v)::l2)) -> kvl_sorted (l1++l2).
Proof.
  intros. 
  replace ((k,v)::l2) with ([(k,v)]++l2) in H by reflexivity.
  apply kvl_sorted_elim_list in H. apply H.
Qed.

Lemma kvl_sorted_elim_common_head : forall (X: Type) (n: nat) (v: X) (l1 l2 l3 l4: list (nat * X)),
  kvl_sorted (l1++(n, v)::l2) ->
  kvl_sorted (l3++(n, v)::l4) ->
  l1++(n, v)::l2 = l3++(n, v)::l4 ->
  l2 = l4.
Proof.
  intros. generalize dependent l3.
  induction l1.
  Case "l1 = []".
    intros.
    simpl in *.
    destruct l3.
    SCase "l3 = []".
      simpl in *.
      inversion H1. reflexivity.
    SCase "l3 = p::l3".
      destruct p.
      rewrite <- app_comm_cons in H1. inversion H1.
      rewrite H3 in H0.
      rewrite <- app_comm_cons in H0.
      apply kvl_sorted_key_across_app in H0.
      apply n_lt_n_inversion with (n := n0). assumption.
  Case "l1 = a::l1".
    intros.
    simpl in *.
    destruct l3.
    SCase "l3 = []".
      simpl in *.
      destruct a.
      inversion H1. rewrite H3 in H.
      apply kvl_sorted_key_across_app in H.
      apply n_lt_n_inversion with (n := n0). rewrite <- H3 in H. assumption.
    SCase "l3 = p::l3".
      rewrite <- app_comm_cons in H1.
      inversion H1.
      apply IHl1 with (l3 := l3).
      destruct a.
      apply list_tail_is_sorted in H. apply H.
      rewrite <- app_comm_cons in H0.
      destruct p.
      apply list_tail_is_sorted in H0.
      apply H0.
      apply H4.
Qed.

Theorem insert_preserves_sort : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> kvl_sorted (insert_into_list k v l).
Proof.
  intros. induction H.
  Case "kvl_sorted_0". simpl. apply kvl_sorted_1.
  Case "kvl_sorted_1". simpl. 
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n". apply kvl_sorted_1.
      SSCase "k != n". apply kvl_sorted_cons. apply kvl_sorted_1.
                       apply blt_nat_true. omega.
    SCase "k > n". apply kvl_sorted_cons. apply kvl_sorted_1.
    	apply blt_nat_true. omega.
  Case "kvl_sorted_cons".
    apply blt_nat_true in H0.
    simpl. remember (ble_nat k n1) as klen1.
    destruct klen1; symmetry in Heqklen1; [apply ble_nat_true in Heqklen1 | apply ble_nat_false in Heqklen1].
    SCase "k <= n1". remember (beq_nat k n1) as keqn1.
      destruct keqn1; symmetry in Heqkeqn1; [apply beq_nat_true_iff in Heqkeqn1 | apply beq_nat_false_iff in Heqkeqn1].
      SSCase "k = n1".
        apply kvl_sorted_cons. apply H. apply blt_nat_true. omega.
      SSCase "k != n1".
        apply kvl_sorted_cons. apply kvl_sorted_cons. apply H. apply blt_nat_true. apply H0.
        apply blt_nat_true. omega.
    SCase "k > n1". simpl in IHkvl_sorted. remember (ble_nat k n2) as klen2. 
      destruct klen2; symmetry in Heqklen2; [apply ble_nat_true in Heqklen2 | apply ble_nat_false in Heqklen2].
      SSCase "k <= n2". remember (beq_nat k n2) as keqn2.
        destruct keqn2; symmetry in Heqkeqn2; [apply beq_nat_true_iff in Heqkeqn2 | apply beq_nat_false_iff in Heqkeqn2].
        SSSCase "k = n2".
          apply kvl_sorted_cons. subst.
          eapply sort_ignores_value. apply H.
          apply blt_nat_true. omega.
        SSSCase "k != n2". 
          apply kvl_sorted_cons. apply kvl_sorted_cons. apply H.
          apply blt_nat_true. omega.
          apply blt_nat_true. omega.
     SSCase "k > n2". 
       apply kvl_sorted_cons. apply IHkvl_sorted.
       apply blt_nat_true. omega.
Qed.

Theorem insert_preserves_sort_cons : forall (X: Type) (l: list (nat * X)) (k1 k2: nat) (v1 v2: X),
  k1 < k2 -> kvl_sorted ((k1,v1)::l) -> kvl_sorted ((k1,v1)::insert_into_list k2 v2 l).
Proof.
  induction l.
  Case "l = []".
    intros.
    simpl.
    apply kvl_sorted_cons. apply kvl_sorted_1. apply blt_nat_true. assumption.
  Case "l = a::l".
    intros.
    destruct a.
    simpl. remember (ble_nat k2 n) as k2len. 
    destruct k2len; symmetry in Heqk2len; [apply ble_nat_true in Heqk2len | apply ble_nat_false in Heqk2len].
    SCase "k2 <= n". remember (beq_nat k2 n) as k2eqn.
      destruct k2eqn; symmetry in Heqk2eqn; [apply beq_nat_true_iff in Heqk2eqn | apply beq_nat_false_iff in Heqk2eqn].
      SSCase "k2 = n".
        subst.
        apply kvl_sorted_cons.
        inversion H0. subst.
        apply sort_ignores_value with (v1 := x) (v2 := v2). apply H3.
        apply blt_nat_true. omega.
      SSCase "k2 < n".
        apply kvl_sorted_cons.
        apply kvl_sorted_cons.
        apply list_tail_is_sorted in H0. apply H0.
        apply blt_nat_true. omega.
        apply blt_nat_true. omega.
    SCase "k2 > n".
      apply kvl_sorted_cons.
      apply IHl.
      inversion H0.
      subst. apply blt_nat_true in H7. omega.
      apply list_tail_is_sorted in H0.
      apply H0.
      apply blt_nat_true. inversion H0.
      subst. apply blt_nat_true in H7. omega.
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

Lemma split_preserves_sort : forall (X: Type) (l l1 l2: list (nat * X)),
  l1 ++ l2 = l -> kvl_sorted l -> kvl_sorted l1 /\ kvl_sorted l2.
Proof.
  intros.  rewrite <- H in H0. apply kvl_sorted_app in H0. apply H0.
Qed.

Theorem split_list_preserves_sort : forall (X: Type) (b: nat) (l l1 l2: list (nat * X)),
  kvl_sorted l -> length l1 = b -> l1 ++ l2 = l -> split_list b l = (l1, l2)
  -> kvl_sorted l1 /\ kvl_sorted l2.
Proof.
  intros.
  apply split_preserves_sort with (l := l); assumption.
Qed.

Lemma app_list_eq_list_list : forall (X: Type) (l1 l2: list X),
  l1 ++ l2 = l1 -> l2 = [].
Proof.
  intros.
  induction l1. simpl in H. apply H.
  apply IHl1. simpl in H. SearchAbout [cons].
  inversion H. rewrite H1. apply H1.
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

Lemma sorted_all_keys_below_app_cons : forall (X: Type) (l1 l2: list (nat*X)) (k: nat) (v1: X), 
  kvl_sorted (l1++(k, v1)::l2) -> all_keys X (below k) (l1).
Proof.
  induction l1.
  Case "l1 = []".
    intros. apply ak_empty. 
  Case "l1 = a::l1". destruct a.
    intros.
    simpl in H.
    apply ak_next.
    eapply IHl1.
      apply list_tail_is_sorted in H. apply H.
    unfold below. apply blt_nat_true.
    apply kvl_sorted_key_across_app in H. 
    omega.
Qed.

Lemma kvl_sorted_after_replace_head_with_zero : forall (X: Type) (k: nat) (v: X) (l: list (nat * X)),
  kvl_sorted( (k, v)::l ) -> kvl_sorted( (0, v)::l).
Proof.
  intros.
  inversion H.
  constructor.
  apply kvl_sorted_cons.
    assumption.
    rewrite blt_nat_true. rewrite blt_nat_true in H4. omega.
Qed.

Lemma cut_list_right_above : forall (X: Type) (b k: nat) (v: X) (l1 l2 l3: list (nat*X)),
  kvl_sorted(l1++(k,v)::l2) ->
  length l1 <= b ->
  cut_list_right b (l1++(k,v)::l2) = l3 ->
  all_keys X (above k) (l3).
Proof.
  induction b.
  Case "b = 0".
    intros.
    apply length_gt_0_impl_nil in H0. subst.
    simpl in *.
    apply sorted_all_keys_above_cons. assumption.
  Case "b = S b".
    intros.
    destruct l1.
    SCase "l1 = []".
      simpl in *. apply sorted_all_keys_above_cons in H.
      inversion H.
      subst.
      apply cut_right_preserves_all_keys.
      apply H4.
    SCase "l1 = p::l1".
      destruct p. rewrite <- app_comm_cons in *.
      simpl in H1.
      eapply IHb.
        apply list_tail_is_sorted in H. apply H.
        simpl in H0. omega.
        apply H1.
Qed.

