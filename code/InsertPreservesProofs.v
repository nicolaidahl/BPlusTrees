Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export ValidBPlusTree.
Require Export InsertProofs.



Lemma insert_leaf_preserves_min_fan_out : forall {X: Type} b k v o counter l l', 
  valid_sub_bplustree b X (bptLeaf b X l) ->
  insert' counter k v (bptLeaf b X l) = (bptLeaf b X l', o) ->
  length l' >= b.
Proof.
  intros. induction H.
  Case "tree is leaf".
    admit.
  Case "tree is node".
    apply insert_into_node_impl_leaf_false in H0. inversion H0.
    constructor; try assumption.
    destruct b. exfalso. omega.
    omega.
Qed.
  


Theorem insert_preserves_tree_validity : forall (b: nat) (X: Type) (tree: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X tree -> valid_bplustree b X (insert k v tree).
Proof.
  admit.
Admitted.

(*
  intros. induction H.
  Case "root_is_a_leaf".
    unfold insert. remember (insert' (height (bptLeaf b X l)) k v (bptLeaf b X l)) as insert'. destruct insert'. destruct o.
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
            apply valid_leaf; try assumption. symmetry in Heqinsert'. 
            apply insert_leaf_preserves_min_fan_out in Heqinsert'. omega.
            apply valid_leaf; try assumption. symmetry in Heqinsert'.
            apply split_leaf_impl_length_max_fan_out in Heqinsert'. omega.
            eapply insert_leaf_preserves_max_fan_out. apply Heqinsert'.
            eapply insert_leaf_preserves_sort. apply H1. apply Heqinsert'.
          SSSSCase "valid sub node".
            apply ex_falso_quodlibet. eapply insert_leaf_split_never_node. right. apply Heqinsert'.
      SSCase "all trees equal height".
        admit.
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
*)



