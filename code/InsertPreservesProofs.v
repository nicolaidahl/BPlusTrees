Require Import BPlusTree.
Require Import HelperProofs.
Require Import SortingProofs.
Require Import ValidBPlusTree.


Lemma insert_leaf_preserves_min_fan_out : forall {X: Type} b k v o l l', 
  (bptLeaf b X l', o) = insert' k v (bptLeaf b X l) ->
  length l' >= b.
Proof. Admitted.

Lemma insert_leaf_preserves_max_fan_out : forall {X: Type} b k v o l l', 
  (bptLeaf b X l', o) = insert' k v (bptLeaf b X l) ->
  length l' <= b * 2.
Proof. Admitted.

Lemma insert_leaf_preserves_sort : forall {X: Type} b k v o l l', 
  kvl_sorted l -> (bptLeaf b X l', o) = insert' k v (bptLeaf b X l) ->
  kvl_sorted l'.
Proof. Admitted.

Lemma insert_leaf_split_preserves_min_fan_out : forall {X: Type} b k v t n l l', 
  (t, Some (n, bptLeaf b X l')) = insert' k v (bptLeaf b X l) ->
  length l' >= b.
Proof. Admitted.

Lemma insert_leaf_split_preserves_max_fan_out : forall {X: Type} b k v t n l l', 
  (t, Some (n, bptLeaf b X l')) = insert' k v (bptLeaf b X l) ->
  length l' <= b * 2.
Proof. Admitted.

Lemma insert_leaf_split_preserves_sort_right : forall {X: Type} b k v t n l l', 
  kvl_sorted l -> (t, Some (n, bptLeaf b X l')) = insert' k v (bptLeaf b X l) ->
  kvl_sorted l'.
Proof. Admitted.


Lemma insert_leaf_split_never_node : forall {X: Type} b k v t o n l l', 
  ((t, Some (n, bptNode b X l')) = insert' k v (bptLeaf b X l) \/
  (bptNode b X l', o) = insert' k v (bptLeaf b X l)) ->
  False.
Proof. Admitted.

Lemma insert_leaf_split_ensures_n_positive : forall {X: Type} b k v n t l l',
  kvl_sorted l -> (t, Some (n, l')) = insert' k v (bptLeaf b X l) ->
  n > 0.
Proof.
Admitted.

Theorem insert_preserves_valid_bplustree : forall (b: nat) (X: Type) (tree: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X tree -> valid_bplustree b X (insert k v tree).
Proof.
  intros. induction H.
  Case "root_is_a_leaf".
    unfold insert. remember (insert' k v (bptLeaf b X l)) as insert'. destruct insert'. destruct o.
    SCase "o = Some(key, right)".
      destruct p. apply valid_root_node; try assumption; try (simpl; omega). 
      SSCase "all_values valid subtree".
        apply av_next. apply av_next. apply av_empty. 
        SSSCase "is the option tree valid".
          induction b1.
          SSSSCase "valid sub leaf".
            apply valid_leaf. assumption. eapply insert_leaf_split_preserves_min_fan_out. apply Heqinsert'.
            eapply insert_leaf_split_preserves_max_fan_out. apply Heqinsert'.
            eapply insert_leaf_split_preserves_sort_right. apply H1. apply Heqinsert'.
          SSSSCase "valid sub node".
            apply ex_falso_quodlibet. eapply insert_leaf_split_never_node. left. apply Heqinsert'.
        SSSCase "is the non-option tree valid".
          induction b0.
          SSSSCase "valid sub leaf".
            apply valid_leaf; try assumption. eapply insert_leaf_preserves_min_fan_out. apply Heqinsert'.
            eapply insert_leaf_preserves_max_fan_out. apply Heqinsert'.
            eapply insert_leaf_preserves_sort. apply H1. apply Heqinsert'.
          SSSSCase "valid sub node".
            apply ex_falso_quodlibet. eapply insert_leaf_split_never_node. right. apply Heqinsert'.
      SSCase "kvl sorted".
        eapply insert_leaf_split_ensures_n_positive in Heqinsert'. 
        apply kvl_sorted_cons. apply kvl_sorted_1. apply blt_nat_true. omega. apply H1.
      SSCase "valid_splits".
        apply valid_p. admit.
        apply valid_ep. admit.
    SCase "o = None".
      admit.
  Case "valid_root_node".
    admit.
    
  
Admitted.
