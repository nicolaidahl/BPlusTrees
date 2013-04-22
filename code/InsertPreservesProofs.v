Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.

Theorem insert_preserves_valid_bplustree : forall (b: nat) (X: Type) (t: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> valid_bplustree b X (insert k v t).
Proof.
  intros. induction H. 
  Case "root_is_a_leaf". admit.
  
    (* unfold insert. remember (insert' k v (bptLeaf b X l)) as insert'.
    destruct insert'. inversion Heqinsert'. remember (insert_leaf b k v l) as insert_leaf.
    destruct insert_leaf. destruct o0. remember (head_key l1) as head_key.
    destruct head_key. inversion H3. *)

  Case "valid_root_node". admit.
Admitted.
