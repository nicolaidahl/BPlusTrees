Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.

Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall skb v l, appears_in_kvl sk l -> appears_in_kvl sk ((skb, v)::l).
  
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

Lemma insert_leaf_cons_lt_overflow : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l l1 l2: list (nat * X)),
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

Theorem size_of_kvl: forall {X: Type} {b: nat} (leaf: list (nat * X)) (k: nat) (v: X), 
  not (appears_in_kvl k leaf) -> length leaf = b * 2 -> 
  ble_nat (length (insert_into_list k v leaf)) (b * 2) = false.
Proof. Admitted.


Theorem split_insert_right : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k kb: nat) (v vb: X),
  b > 0 -> kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index b leaf = Some (kb, vb) -> 
  k > kb -> length leaf = mult b 2 -> 
  insert_leaf b k v leaf = (left, Some kvl) -> appears_in_kvl k kvl.
Proof.
  intros X b leaf left kvl k kb v vb. intros Hb Hsort Happears Hcentral Hkkb Hlength Hinsertion.
  induction leaf. 
  Case "leaf = nil".
	  simpl in Hlength. admit.
  Case "leaf = x :: leaf". 
     Admitted.
    
Theorem split_insert_left : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k k1 kb: nat) (v vb: X),
  kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index b leaf = Some (kb, vb) -> 
  k < kb -> length leaf = mult b 2 -> 
  insert_leaf b k v leaf = (left, Some kvl) /\ appears_in_kvl k left.

Theorem split_insert_normal : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k: nat) (v: X),
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
    
