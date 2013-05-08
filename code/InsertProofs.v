Require Export BPlusTree.
Require Export HelperProofs.

(* Proofs about height *)
Lemma height_of_parent_one_bigger: forall (X:Type) b kpl k v l,
  kpl = ((k, v)::l) -> all_values_eq_prop (bplustree b X) (equal_height) kpl ->
  S (height v) = height (bptNode b X kpl).
Proof.
  intros. induction H0; try inversion H; reflexivity.
Qed.

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