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
        apply ex_falso_quodlibet. apply H. apply aik_here.
      SSCase "k < n".
        simpl. omega.
    SCase "k > n".
      simpl.
      apply n_lt_m__Sn_lt_Sm.
      apply IHl. unfold not. intro. apply H. apply aik_later. apply H0.
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

Lemma insert_into_list_length_gt_iil_length : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> length l <= length (insert_into_list k v l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. omega.
  Case "l = a::l". destruct a.
    simpl.
    remember (ble_nat k n) as klen.
    destruct klen.
      remember (beq_nat k n) as keqn.
      destruct keqn; simpl.
        omega.
        omega.
      simpl.
      apply le_n_S.
      apply IHl.
      apply list_tail_is_sorted in H.
      apply H.
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
        apply H0. apply aik_here.
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
      apply aik_later. apply H2.
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
        apply H0. apply aik_here.
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
      apply aik_later. apply H2.
      simpl in H1. omega.
Qed.

Lemma override_in_list_preserves_length : forall (X: Type) (k: nat) (v: X) (kpl: list (nat * X)),
  kvl_sorted kpl ->
  appears_in_kvl k kpl ->
  length kpl = length (insert_into_list k v kpl).
Proof.
  intros. induction H0. 
  Case "aik_here".
    simpl. rewrite ble_nat_symm. rewrite <- beq_nat_refl. reflexivity.
  Case "aik_later".
    apply appears_in_kvl_app in H0. do 3 destruct H0.  subst. 
    remember ((k0, v0) :: witness ++ (k, witness1) :: witness0). rewrite Heql in H.
    assert (kvl_sorted (witness ++ (k, witness1) :: witness0)).
      apply list_tail_is_sorted in H. assumption.
    apply kvl_sorted_key_across_app in H. subst. simpl.
    assert (ble_nat k k0 = false).
      apply ble_nat_false. omega.
    rewrite H1. simpl. apply eq_remove_S. apply IHappears_in_kvl. assumption.
Qed.
    

Lemma override_in_list_app : forall (X: Type) (k: nat) (v1 v2: X) (l1 l2: list (nat * X)),
  kvl_sorted (l1 ++ (k, v1)::l2) -> 
  insert_into_list k v2 (l1 ++ (k, v1)::l2) = l1 ++ (k,v2)::l2.
Proof.
  intros. induction l1. 
  Case "l1 = []".
    simpl. rewrite ble_nat_symm. rewrite <- beq_nat_refl. reflexivity.
  Case "l1 = a :: l1".
    destruct a. simpl. assert (kvl_sorted (((n, x) :: l1) ++ (k, v1) :: l2)) by assumption. 
    apply kvl_sorted_key_across_app in H. 
    assert (ble_nat k n = false).
      apply ble_nat_false. omega. rewrite H1. apply cons_remove. apply IHl1.
      apply list_tail_is_sorted in H0. apply H0.
Qed.
  
Lemma insert_into_list_prepend_first: forall {X: Type} k n (x: X) v l,
  n < k ->
  insert_into_list k v ((n, x) :: l) = (n, x) :: insert_into_list k v l.
Proof.
  intros. simpl. remember (ble_nat k n). destruct b. remember (beq_nat k n). destruct b;
  (symmetry in Heqb; apply ble_nat_true in Heqb; exfalso; omega).
  reflexivity.
Qed.
  
Lemma insert_into_list_middle : forall (X: Type) (k1 k2 new_key: nat) (v1 v2 new_value: X) (l1 l2: list (nat * X)), 
  k1 < new_key < k2 ->
  kvl_sorted (l1++(k1, v1)::(k2, v2)::l2) ->
  insert_into_list new_key new_value (l1++(k1, v1)::(k2, v2)::l2) = (l1++(k1, v1)::(new_key, new_value)::(k2, v2)::l2).
Proof.
  intros. induction l1. simpl.
  Case "l1 = []".  
    assert (ble_nat new_key k1 = false).
      apply ble_nat_false. omega.
    rewrite H1. 
    assert (ble_nat new_key k2 = true).
      apply ble_nat_true. omega.
    rewrite H2. 
    assert (beq_nat new_key k2 = false).
      apply beq_nat_false_iff. omega. rewrite H3. reflexivity.
  Case "l1 = a l1".
    destruct a. repeat rewrite <- app_comm_cons in H0.
    repeat rewrite <- app_comm_cons.
    rewrite insert_into_list_prepend_first. apply cons_remove.
    apply IHl1. apply list_tail_is_sorted in H0. assumption.
    apply kvl_sorted_key_across_app in H0. omega.
Qed.

Lemma insert_into_list_last : forall (X: Type) (k1 new_key: nat) (v1 new_value: X) (l1: list (nat * X)), 
  k1 < new_key ->
  kvl_sorted (l1++[(k1, v1)]) ->
  insert_into_list new_key new_value (l1++[(k1, v1)]) = l1++[(k1, v1), (new_key, new_value)].
Proof.
  intros. induction l1. simpl.
  Case "l1 = []".
    assert (ble_nat new_key k1 = false). apply ble_nat_false. omega.
    rewrite H1. reflexivity.
  Case "l1 = a :: l1".
    destruct a. repeat rewrite <- app_comm_cons. rewrite insert_into_list_prepend_first.
    apply cons_remove. apply IHl1.
    repeat rewrite <- app_comm_cons in H0. apply list_tail_is_sorted in H0. assumption.
    apply kvl_sorted_key_across_app in H0. omega.
Qed.


Lemma insert_into_list_override : forall (X: Type) (k: nat) (v1 v2: X) (l1 l2: list (nat * X)),
  kvl_sorted (l1++(k, v1)::l2) ->
  insert_into_list k v2 (l1++(k, v1)::l2) = (l1++(k, v2)::l2).
Proof.
  intros. induction l1.
  Case "l1 = []". 
    simpl. rewrite ble_nat_symm. rewrite <- beq_nat_refl. reflexivity.
  Case "l1 = a l1".
    repeat rewrite <- app_comm_cons in H.
    destruct a. 
    repeat rewrite <- app_comm_cons. rewrite insert_into_list_prepend_first. apply cons_remove.
    apply IHl1. apply list_tail_is_sorted in H. assumption.
    apply kvl_sorted_key_across_app in H. omega.
Qed.
    


Lemma insert_into_list_last_twice : forall (X: Type) (k1 k2: nat) (t1 t1' t2: X) (l: list (nat * X)),
  kvl_sorted (l ++ [(k1, t1)]) ->
  k1 < k2 ->
  insert_into_list k1 t1' (insert_into_list k2 t2 (l ++ [(k1, t1)])) = l ++ [(k1, t1'), (k2, t2)].
Proof.
  intros.
  assert (kvl_sorted (insert_into_list k2 t2 (l ++ [(k1, t1)]))).
    apply insert_preserves_sort.
    assumption.
  assert (kvl_sorted(insert_into_list k1 t1' (insert_into_list k2 t2 (l ++ [(k1, t1)])))).
    apply insert_preserves_sort. apply insert_preserves_sort.
    assumption.
  rewrite insert_into_list_last in *; try assumption.
  rewrite insert_into_list_override in *; try assumption.
  reflexivity.
Qed.

Lemma insert_into_list_middle_twice : forall (X: Type) (k1 k2 k3: nat) (t1 t1' t2 t3: X) (l1 l2: list (nat * X)),
  kvl_sorted (l1 ++ (k1, t1)::(k3, t3)::l2) ->
  k1 < k2 < k3 ->
  insert_into_list k1 t1' (insert_into_list k2 t2 (l1 ++ (k1, t1)::(k3, t3)::l2)) = l1 ++ (k1, t1')::(k2, t2)::(k3, t3)::l2.
Proof.
  intros.
  assert (kvl_sorted(insert_into_list k2 t2 (l1 ++ (k1, t1) :: (k3, t3) :: l2))).
    apply insert_preserves_sort.
    assumption.
  assert (kvl_sorted(insert_into_list k1 t1' (insert_into_list k2 t2 (l1 ++ (k1, t1) :: (k3, t3) :: l2)))).
    apply insert_preserves_sort. apply insert_preserves_sort.
    assumption.
  rewrite insert_into_list_middle in *; try assumption.
  rewrite insert_into_list_override in *; try assumption.
  reflexivity.
Qed.

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
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 < k2 -> 
  length((k2,v2)::l) < mult b 2 -> 
  insert_leaf b k1 v1 ((k2, v2) :: l) = ((k1,v1)::(k2,v2)::l, None).
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
  b <> 0 -> kvl_sorted ((k2,v2)::l) -> k1 > k2 -> 
  length((k2,v2)::l) < mult b 2 -> 
  insert_leaf b k1 v1 ((k2, v2) :: l) = ((k2,v2):: insert_into_list k1 v1 l, None).
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





Lemma find_subtree_after_replace: forall (X: Type) (b key sk: nat) (t1 t2: bplustree b X) (kpl: list (nat * bplustree b X)),
  kvl_sorted kpl ->
  find_subtree sk kpl = Some (key, t1) ->
  find_subtree sk (insert_into_list key t2 kpl) = Some (key, t2).
Proof.
  intros. 
  remember (bptNode b X kpl) as node.
  assert (kvl_sorted kpl) by assumption. 
  apply insert_preserves_sort with (k:=key)(v:=t2) in H.
  remember (insert_into_list key t2 kpl) as kpl'. 
  assert (kpl' = insert_into_list key t2 kpl) by assumption.
  
  assert (find_subtree sk kpl = Some (key, t1)) by assumption.
  
  apply find_subtree_impl_kpl_app in H0; do 2 destruct H0. destruct H0.
  rewrite H0 in H3. destruct H4; subst.

  Case "key <= sk ... t2 is last tree t2".
    apply find_subtree_key_in_last in H3.
    rewrite override_in_list_app. apply find_subtree_key_in_last.
    rewrite override_in_list_app in H. apply H. assumption. assumption. assumption. assumption.
  Case "key <= sk < k2 ... is in t2".
    destruct H4. do 3 destruct H0. subst. 
    
    apply find_subtree_key_in_middle in H3.
    rewrite override_in_list_app in H.  
     
    rewrite override_in_list_app.
    apply find_subtree_key_in_middle; assumption. assumption. apply H1. assumption.
Qed.

Lemma insert_into_list_later_than_first: forall (X: Type) b k1 k2 t1 t2 
                                       (l: list (nat * bplustree b X)), 
  k1 < k2 ->
  exists l1, exists l2, insert_into_list k2 t2 ((k1, t1) :: l) = (k1, t1) :: l1 ++ (k2, t2) :: l2.
Proof.
  intros. 
  simpl.
  
  assert (ble_nat k2 k1 = false).
    apply ble_nat_false. omega.
  rewrite H0.
  remember (insert_into_list k2 t2 l).
  symmetry in Heql0. apply insert_into_list_app in Heql0. destruct Heql0. destruct H1.
  exists witness. exists witness0. rewrite H1. reflexivity.
Qed.


Lemma find_subtree_insert_into_list_remove_inner_cons: forall {X: Type} b k1 k2 k3 k4 t1 t2 t3 t4 sk
    (l: list(nat * bplustree b X)),
  kvl_sorted ((k1, t1) :: (k2, t2) :: l) ->
  k2 <= k3 ->
  find_subtree sk (insert_into_list k3 t3 ((k2, t2) :: l)) = Some (k4, t4) ->
  find_subtree sk ((k1, t1) :: insert_into_list k3 t3 ((k2, t2) :: l)) = Some (k4, t4).
Proof.
  intros. 
  assert (kvl_sorted ((k1, t1) :: (k2, t2) :: l)) by assumption.
  assert ((k1, t1) :: (k2, t2) :: l = (k1, t1) :: [] ++ (k2, t2) :: l).
    reflexivity.
  rewrite H3 in H2.
  apply kvl_sorted_key_across_app in H2. clear H3.
  assert (k1 < k3) by omega.
  
  remember (beq_nat k2 k3). destruct b0.
  Case "k2 = k3".
    symmetry in Heqb0. apply beq_nat_true in Heqb0. subst. 
    assert ((k3, t2) :: l = [] ++ (k3, t2) :: l) by reflexivity.
    rewrite H4.
    rewrite insert_into_list_override with (l1 := []).
    rewrite H4 in H1. 
    rewrite insert_into_list_override with (l1 := []) in H1.
    assert (find_subtree sk ((k3, t3) :: l) = Some (k4, t4)) by assumption.
    apply find_subtree_impl_sk_greater_than_first in H1.  
    simpl. 
    assert (ble_nat k1 sk && blt_nat sk k3 = false).
      assert (blt_nat sk k3 = false). 
        apply blt_nat_false. omega.
      rewrite H6. destruct (ble_nat k1 sk); reflexivity.
    rewrite H6. apply H5.
      
    apply list_tail_is_sorted in H.
    simpl. apply sort_ignores_value with (v2:=t3) (v1:= t2).
    assumption.
    apply list_tail_is_sorted in H. assumption.
    apply list_tail_is_sorted in H. assumption.
  Case "k2 < k3".
    remember (insert_into_list k3 t3 ((k2, t2) :: l)) as kpl'.
    symmetry in Heqkpl'. 
    assert (kvl_sorted kpl').
      rewrite <- Heqkpl'. apply insert_preserves_sort.
      apply list_tail_is_sorted in H. assumption.
    assert (k2 < k3).
      symmetry in Heqb0. apply beq_nat_false_iff in Heqb0. omega.
    apply insert_into_list_later_than_first with (t1:=t2)(t2:=t3)(l:=l) in H5.
    do 2 destruct H5. rewrite Heqkpl' in H5. rewrite H5. rewrite H5 in H1.
    apply find_subtree_later3 with (l1:=[]).
    
    rewrite H5 in H4. simpl. apply kvl_sorted_cons. assumption. apply blt_nat_true. assumption.
    apply find_subtree_impl_sk_greater_than_first in H1. omega.
    rewrite H5 in H4. assumption.
    simpl. assumption. 

Qed.
    
 

  




Lemma find_subtree_after_inserting_greater_element: forall (X: Type) (b k1 k2 sk: nat) (t1 t2: bplustree b X) (kpl: list (nat * bplustree b X)),
  1 <= length kpl ->
  kvl_sorted kpl ->
  find_subtree sk kpl = Some (k1, t1) ->
  sk < k2 ->
  find_subtree sk (insert_into_list k2 t2 kpl) = Some (k1, t1).
Proof.
  intros.
  assert (find_subtree sk kpl = Some (k1, t1)) by assumption.
  apply find_subtree_returns_a_lesser_key in H3; try assumption.
  induction H0.
  Case "kvl_sorted_0".
    inversion H.
  Case "kvl_sorted_1".
    apply find_subtree_one_impl_found in H1. destruct H1. subst. simpl.
    assert (ble_nat k2 k1 = false).
      apply ble_nat_false. omega.
    rewrite H0. simpl.
    assert (ble_nat k1 sk = true).
      apply ble_nat_true. omega.
    assert (blt_nat sk k2 = true).
      apply blt_nat_true. omega.
    rewrite H1. rewrite H4. simpl. reflexivity. left. omega.
  Case "kvl_sorted_cons".
    assert (kvl_sorted ((n1,x1):: (n2, x2) :: lst)).
      apply kvl_sorted_cons. assumption. assumption.
    remember (ble_nat n2 k2). destruct b0.
    SCase "n2 <= k2".
      assert (n1 < k2).
        assert ((n1, x1) :: (n2, x2) :: lst = (n1, x1) :: [] ++ (n2, x2) :: lst).
          reflexivity.
        rewrite H6 in H5.
        apply kvl_sorted_key_across_app in H5. symmetry in Heqb0. apply ble_nat_true in Heqb0.
        omega.
      rewrite insert_into_list_prepend_first; try assumption. 
      remember (ble_nat n2 k1). destruct b0.
      SSCase "n2 <= k1".
        apply find_subtree_later in H1. apply IHkvl_sorted in H1.
        apply find_subtree_insert_into_list_remove_inner_cons.  assumption.
        symmetry in Heqb0. apply ble_nat_true in Heqb0. apply blt_nat_true in H4. 
        omega. assumption.
        simpl. omega.
        symmetry in Heqb0. apply ble_nat_true in Heqb0. apply blt_nat_true in H4. right.
        symmetry in Heqb1. apply ble_nat_true in Heqb1. omega.
        eapply kvl_sorted_cons in H0. apply H0. assumption.
      SSCase "n2 > k1".
        symmetry in Heqb0. symmetry in Heqb1. apply ble_nat_true in Heqb0.
        simpl.
        remember (ble_nat k2 n2). destruct b0.
        SSSCase "k2 <= n2".
          remember (beq_nat k2 n2). destruct b0. remember (ble_nat n1 sk). destruct b0.
          remember (blt_nat sk k2). destruct b0. simpl.
          simpl in H1. rewrite <- Heqb4 in H1. symmetry in Heqb3. apply beq_nat_true_iff in Heqb3.
          rewrite <- Heqb3 in H1. rewrite <- Heqb5 in H1. simpl in H1. assumption.
          simpl.
          symmetry in Heqb5. apply blt_nat_false in Heqb5. exfalso. omega.
          apply find_subtree_before_head_None with (k:=sk) in H5. rewrite H5 in H1. inversion H1.
          symmetry in Heqb4. apply ble_nat_false in Heqb4. omega.
          remember (ble_nat n1 sk). destruct b0. remember (blt_nat sk k2). destruct b0.
          simpl. simpl in H1.
          symmetry in Heqb2. apply ble_nat_true in Heqb2. assert (n2 = k2). omega.
          rewrite H7 in H1. rewrite <- Heqb5 in H1. rewrite <- Heqb4 in H1. simpl in H1.
          assumption.
          symmetry in Heqb5. apply blt_nat_false in Heqb5. exfalso. omega.
          symmetry in Heqb4. apply ble_nat_false in Heqb4. symmetry in Heqb2. apply ble_nat_true in Heqb2.
          apply ble_nat_false in Heqb1. symmetry in Heqb3. apply beq_nat_false_iff in Heqb3. exfalso. omega.
        SSSCase "k2 > n2".
          remember (ble_nat n1 sk). destruct b0. 
          SSSSCase "n1 <= sk".
            remember (blt_nat sk n2). destruct b0. 
            SSSSSCase "sk < n2".
              simpl. simpl in H1.
              symmetry in Heqb2. apply ble_nat_false in Heqb2. rewrite <- Heqb3 in H1. 
              symmetry in Heqb4.
              rewrite Heqb4 in H1. simpl in H1. assumption.
            SSSSSCase "n2 <= sk".
              rewrite ble_nat_false in Heqb1. symmetry in Heqb2.  apply ble_nat_false in Heqb2. 
              symmetry in Heqb3. apply ble_nat_true in Heqb3. symmetry in Heqb4. apply blt_nat_false in Heqb4.
              apply blt_nat_true in H4. apply find_subtree_is_first in H1.
              exfalso. omega. omega. omega. assumption.
          SSSSCase "n1 > sk".
            eapply find_subtree_before_head_None in H5. rewrite H5 in H1. inversion H1.
            symmetry in Heqb3. apply ble_nat_false in Heqb3. omega.
    SCase "n2 > k2".
      apply blt_nat_true in H4.
      symmetry in Heqb0. apply ble_nat_false in Heqb0.
      simpl. remember (ble_nat k2 n1). destruct b0. 
      SSCase "k2 <= n1".
        symmetry in Heqb1. apply ble_nat_true in Heqb1.
        remember (beq_nat k2 n1). destruct b0.
        SSSCase "k2 <= n1".
          symmetry in Heqb2. apply beq_nat_true in Heqb2. subst. 
          apply find_subtree_before_head_None with (k:=sk) in H5. rewrite H5 in H1. inversion H1.
          omega.
        SSSCase "k2 > n1".
          symmetry in Heqb2. apply beq_nat_false in Heqb2. 
          apply find_subtree_before_head_None with (k:=sk) in H5. rewrite H5 in H1. inversion H1.
          omega.
      SSCase "k2 > n1".
        symmetry in Heqb1. apply ble_nat_false in Heqb1. remember (ble_nat k2 n2). destruct b0.
        symmetry in Heqb2. apply ble_nat_true in Heqb2. remember (beq_nat k2 n2). destruct b0.
        symmetry in Heqb3. apply beq_nat_true in Heqb3. subst. exfalso. omega.
        symmetry in Heqb3. apply beq_nat_false in Heqb3. 
        SSSCase "it seems k1 = n1".
          simpl. remember (ble_nat n1 sk). destruct b0. remember (blt_nat sk k2). destruct b0.
          simpl in H1. rewrite <- Heqb4 in H1. 
          assert (blt_nat sk n2 = true).
            symmetry in Heqb5. apply blt_nat_true in Heqb5.
          apply blt_nat_true. omega. rewrite H6 in H1. simpl in H1.
          simpl.
	      assumption. 
	      simpl. symmetry in Heqb5. apply blt_nat_false in Heqb5. exfalso. omega.
	      apply find_subtree_before_head_None with (k:=sk) in H5. rewrite H5 in H1. inversion H1.
	      symmetry in Heqb4. apply ble_nat_false in Heqb4. omega.
	    SSSCase "it seems n2 < k2".
	      symmetry in Heqb2. apply ble_nat_false in Heqb2. exfalso. omega.
Qed.



Lemma child_is_valid_bplustree : forall (X: Type) (b k key: nat) (child: bplustree b X) (kpl: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X kpl) ->
  find_subtree k kpl = Some(key, child) ->
  valid_bplustree b X child.
Proof.
  intros.
  apply find_subtree_impl_kpl_app in H0.
  do 2 destruct H0.
  inversion H0. clear H0.
  rewrite H1 in H.
  inversion H.
  apply all_values_single in H7.
  apply valid_sub_bplustree_impl_valid_bplustree in H7.
  assumption.
Qed.

Lemma insert_leaf_split_preserves_list: forall (X: Type) (b k: nat) (v: X) (l l1 l2: list (nat *X)),
  insert_leaf b k v l = (l1, Some (l2)) ->
  insert_into_list k v l = l1++l2.
Proof.
  intros.
  unfold insert_leaf in H.
  remember (ble_nat (length (insert_into_list k v l)) (b * 2)) as fits_here.
  destruct fits_here.
  Case "fits here".
    inversion H.
  Case "overflow".
    remember (split_list b (insert_into_list k v l)) as sl.
    symmetry in Heqsl.
    destruct sl.
    apply split_list_preserves_lists in Heqsl. inversion H.
    subst.
    apply Heqsl.
Qed.
  
  
  
  
  
  
  
  
  

