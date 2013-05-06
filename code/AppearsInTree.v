Require Export AppearsInKVL.
Require Export BPlusTree.
Require Export ValidBPlusTree.

Inductive appears_in_tree {X:Type} {b: nat} (sk: nat) : bplustree b X -> Prop :=
  | ait_leaf       : forall l,       appears_in_kvl sk l -> appears_in_tree sk (bptLeaf b X l)
  | ait_node_one   : forall k v,     appears_in_tree sk v -> k <= sk ->
                                     appears_in_tree sk (bptNode b X [(k, v)])
  | ait_node_here  : forall k1 k2 v1 v2 l, 
                                     appears_in_tree sk v1 -> k1 <= sk /\ sk < k2 ->
                                     appears_in_tree sk (bptNode b X ((k1, v1)::(k2, v2)::l))
  | ait_node_later : forall x k v l, appears_in_tree sk (bptNode b X ((k, v)::l)) -> k <= sk ->
                                     appears_in_tree sk (bptNode b X (x::(k, v)::l)).

Theorem appears_search_works : forall (b: nat) (X: Type) (t t1: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> 
  appears_in_tree k t -> 
  search k t = Some(v).
Proof.
  intros. induction H0. Admitted.
  
  
  
  
  
  
  
  
  