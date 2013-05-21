Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export ValidBPlusTree.
Require Export InsertProofs.


Theorem insert_preserves_tree_validity : forall (b: nat) (X: Type) (tree: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X tree -> valid_bplustree b X (insert k v tree).
Proof.
  admit.
Admitted.
