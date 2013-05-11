Require Export BPlusTree.
Require Export HelperProofs.
Require Export HeightProofs.
Require Export SortingProofs.
Require Export AppearsInTree.
Require Export FindSubtreeProofs.

(* Proofs about insertion *)
Lemma insert_new_into_list_length_gt_length : forall (X: Type) (k: nat) (v: X) (l: list (nat*X)),
  ~ appears_in_kvl k l ->
  length l < length (insert_into_list k v l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. omega.
  Case "l = a::l". destruct a.
    simpl. remember (ble_nat k n) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n".
      remember (beq_nat k n) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        rewrite Heqkeqn in H.
        apply ex_falso_quodlibet. apply H. apply ai_here.
      SSCase "k < n".
        simpl. omega.
    SCase "k > n".
      simpl.
      apply n_lt_m__Sn_lt_Sm.
      apply IHl. unfold not. intro. apply H. apply ai_later. apply H0.
Qed.

Lemma insert_leaf_not_split_impl_space_left: forall {X: Type} (b: nat) k (v:X) l l',
  ~ appears_in_kvl k l ->
  insert_leaf b k v l = (l', None) -> length l < b * 2.
Proof.
  intros.
  unfold insert_leaf in H0.
  remember (ble_nat (length (insert_into_list k v l)) (b * 2)) as blelen.
  destruct blelen.
  symmetry in Heqblelen. apply ble_nat_true in Heqblelen.
  assert (length l < length (insert_into_list k v l)).
    apply insert_new_into_list_length_gt_length; assumption.
  omega.
  inversion H0.
Qed.

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
  kvl_sorted l -> ~(appears_in_kvl k l ) -> 
  length l < n -> length (insert_into_list k v l) <= n.
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

Lemma override_in_list_preserves_length : forall (X: Type) (k: nat) (v: X) (kpl: list (nat * X)),
  appears_in_kvl k kpl ->
  length kpl = length (insert_into_list k v kpl).
Proof.
  admit.
Admitted.

Lemma override_in_list_app : forall (X: Type) (k: nat) (v1 v2: X) (l1 l2: list (nat * X)),
  kvl_sorted (l1 ++ (k, v1)::l2) -> 
  insert_into_list k v2 (l1 ++ (k, v1)::l2) = l1 ++ (k,v2)::l2.
Proof.
  admit.
Admitted.

Lemma insert_leaf_cons_eq : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat * X)),
  b <> 0 -> kvl_sorted ((k2, v2)::l) -> 
  k1 = k2 -> length((k2,v2)::l) <= mult b 2 -> 
  insert_leaf b k1 v1 ((k2, v2) :: l) = ((k1,v1)::l, None).
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
  b <> 0 -> kvl_sorted ((k2, v2)::l) -> 
  k1 < k2 -> length((k2,v2)::l) = mult b 2 -> 
  insert_leaf b k1 v1 ((k2, v2) :: l) = (let (fst, snd) := split_list b ((k1, v1) :: (k2, v2) :: l) in (fst, Some snd)).
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
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 > k2 -> 
  ~(appears_in_kvl k1 l) -> length((k2,v2)::l) = mult b 2 -> 
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




Lemma insert_into_list_app : forall (X: Type) (k: nat) (v: X) (kpl kpl': list (nat * X)),
  insert_into_list k v kpl = kpl' ->
  exists l1, exists l2, kpl' = l1 ++ (k,v)::l2.
Proof.
  intros. generalize dependent kpl'.
  induction kpl.
  Case "kpl = []".
    intros.
    simpl in H. subst.
    exists []. exists []. reflexivity.
  Case "kpl = a::kpl".
    intros.
    destruct a.
    simpl in H.
    remember (ble_nat k n) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n".
      remember (beq_nat k n) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        rewrite <- H.
        exists []. exists kpl. reflexivity.
      SSCase "k < n".
        rewrite <- H.
        exists []. exists ((n,x)::kpl). reflexivity.
    SCase "k > n".
      destruct kpl'. inversion H.
      inversion H.
      assert ((exists l0 : list (nat * X), exists l3 : list (nat * X),
                insert_into_list k v kpl = l0 ++ (k, v) :: l3) ->
              (exists l0 : list (nat * X), exists l3 : list (nat * X),
                (n, x) :: insert_into_list k v kpl = l0 ++ (k, v) :: l3)).
        intro. do 2 destruct H0.
        exists ((n,x)::witness). exists witness0.
        rewrite <- app_comm_cons. rewrite H0. reflexivity.
      apply H0.
      apply IHkpl.
        reflexivity.
Qed.

Lemma key_at_index_0none_impl_empty: forall (X: Type) l,
  @key_at_index X 0 l = None -> l = [].
Proof. 
  intros. unfold key_at_index in H. destruct l. reflexivity. destruct p. inversion H.
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



