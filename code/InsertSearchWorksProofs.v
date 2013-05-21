Require Export BPlusTree.
Require Export SortingProofs.
Require Export ValidBPlusTree.
Require Export InsertImplAppears.
Require Export InsertPreservesProofs.
Require Export AppearsImplSearchFound.

Theorem insert_search_works: forall {X: Type} {b: nat} (k: nat) (v: X) (t: bplustree b X),
  valid_bplustree b X t ->
  ~ appears_in_tree k t ->
  search k (insert k v t) = Some (v).
Proof.
  intros. remember (insert k v t) as t'; symmetry in Heqt'.
  assert (valid_bplustree b X t').
    apply insert_preserves_tree_validity with (k := k) (v := v) in H;
    subst; assumption.
  apply insert_impl_appears in Heqt'; try assumption.
  apply appears_impl_search_found in Heqt'; assumption. 
Qed.

(* This proof was merely conducted to ensure we were on the right track *)
Theorem insert_search_leaf_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
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
