Require Export ValidBPlusTree.
Require Export SfLib.

Definition member_of_kvlist {X: Type} (sk: nat) (lst: list (nat * X)): Prop :=
  exists n, n = sk. 

Definition not_member_of_kvlist {X: Type} (sk: nat) (lst: list (nat * X)): Prop :=
  forall n, n <> sk.
  
Theorem deletion_in_list_removes_element: forall (b: nat) (X: Type) (sk: nat) (l: list (nat * X)),
  search_leaf sk (delete_from_list sk l) = None.

Theorem deletion_removes_element: forall (b: nat) (X: Type) (sk: nat) (t: bplustree b X),
  valid_bplustree b X (t) ->
  search sk (delete sk t) = None. 
Proof.
  intros b X sk t H.
  inversion H.
  Case "Leaf".
    unfold delete. simpl. remember (blt_nat (length (delete_from_list sk l)) b) as del_length.
    destruct del_length.
    SCase "del_length true".
      simpl. destruct (delete_from_list sk l). simpl. reflexivity. 
      simpl.
 Admitted.
  
Theorem deletion_preserves_invariant: forall (b: nat) (X: Type) (k: nat) (t: bplustree b X),
  valid_bplustree b X (t) -> 
  valid_bplustree b X (delete k t).
Proof.
Admitted.