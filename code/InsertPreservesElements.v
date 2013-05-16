Require Export BPlusTree.
Require Export ValidBPlusTree.

Theorem insert_preserves_elements: forall {X: Type} {b: nat} k (v:X) (t: bplustree b X),
  valid_bplustree b X t -> 
  insert_into_list k v (inorder t) = inorder (insert k v t).
Proof. Admitted.