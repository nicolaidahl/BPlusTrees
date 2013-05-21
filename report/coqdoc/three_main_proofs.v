Theorem insert_search_works: forall {X: Type} {b: nat} (k: nat) (v: X) (t: bplustree b X),
  valid_bplustree b X t ->
  ~ appears_in_tree k t ->
  search k (insert k v t) = Some (v).

Theorem insert_preserves_tree_validity : forall (b: nat) (X: Type) (tree: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X tree -> valid_bplustree b X (insert k v tree).

Theorem insert_preserves_elements: forall {X: Type} {b: nat} k (v:X) (t: bplustree b X),
  valid_bplustree b X t -> 
  insert_into_list k v (inorder t) = inorder (insert k v t).

