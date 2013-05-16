Require Export BPlusTree.
Require Export SortingProofs.
Require Export ValidBPlusTree.
Require Export InsertWorksProofs.
Require Export SearchWorksProofs.

Theorem insert_words: forall {X: Type} {b: nat} (k: nat) (v: X) (t: bplustree b X),
  valid_bplustree b X t ->
  ~ appears_in_tree k t ->
  search k (insert k v t) = Some (v).
Proof.
  intros. remember (insert k v t). symmetry in Heqb0. apply insert_works in Heqb0.
  Case "Search in tree finds some element".
    apply appears_search_works in Heqb0. destruct Heqb0. 
    admit.
    admit.
  assumption. assumption.
Admitted.

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