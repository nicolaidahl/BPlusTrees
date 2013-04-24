Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.

Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall skb v l, appears_in_kvl sk l -> appears_in_kvl sk ((skb, v)::l).
  
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
	  simpl in Hlength. omega.
  Case "leaf = x :: leaf". 
     Admitted.
    



  
Theorem split_insert_left : forall {X: Type} {b: nat} (leaf left kvl: list (nat * X)) (k k1 kb: nat) (v vb: X),
  kvl_sorted leaf -> not (appears_in_kvl k leaf) -> element_at_index b leaf = Some (kb, vb) -> 
  k < kb -> length leaf = mult b 2 -> 
  insert_leaf b k v leaf = (left, Some kvl) /\ appears_in_kvl k left.

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

Lemma insert_into_list_increases_length : forall (X: Type) (l: list (nat * X)) (k n: nat) (v: X),
  kvl_sorted l -> length l = n -> length (insert_into_list k v l) <= S n.
Proof.
  intros. generalize dependent l. induction n; intros.
  simpl.
  Case "n = 0".
    apply length_0_impl_nil in H0. subst. simpl. omega.
  Case "n = S n".
    destruct l. simpl. omega.
    destruct p.
    simpl. remember (ble_nat k n0) as klen.
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n0".
      remember (beq_nat k n0) as keqn.
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn];
      simpl; simpl in H0;  rewrite H0; omega.
    SCase "k > n0".
      simpl. apply le_n_S. apply IHn.
      apply list_tail_is_sorted in H. apply H.
      simpl in H0. inversion H0. reflexivity.
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
    
