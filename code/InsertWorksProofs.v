Require Export BPlusTree.
Require Export HelperProofs.
Require Export SortingProofs.
Require Export HelperFunctions.

Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall skb v l, appears_in_kvl sk l -> appears_in_kvl sk ((skb, v)::l).
  
(*Theorem split_insert_left : forall (X: Type) (b: nat) (kvl: list (nat * X)) (k k1 kb: nat) (v vb: X) (leaf: list (nat * X)),
  kvl_sorted kvl -> not (appears_in_kvl k kvl) -> element_at_index b kvl = Some (kb, vb) -> k < kb ->
  (length kvl) = (mult b 2) -> insert_leaf b k v leaf = bptNode b X left [(k1, right)] /\ appears_in_kvl k left.*)

Theorem insert_into_list_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
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

Theorem insert_leaf_normal : forall (X: Type) (b: nat) (k: nat) (v: X) (kvl: list (nat * X)),
  kvl_sorted kvl -> length(kvl) < pred(mult b 2)-> 
  insert_leaf b k v kvl = (insert_into_list k v kvl, None).
Proof.
  admit.
Admitted.

Theorem insert_leaf_split : forall (X: Type) (b: nat) (k: nat) (v: X) (kvl kvl1 kvl2: list (nat * X)),
  kvl_sorted kvl -> length(kvl) = mult b 2 -> 
  (kvl1, kvl2) = split_list b (insert_into_list k v kvl1) -> 
  insert_leaf b k v kvl = (kvl1, Some kvl2).
Proof.
  admit.
Admitted.

Theorem insert_works : forall (b: nat) (X: Type) (t: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> search k (insert k v t) = Some v.
Proof.
  intros.
  induction H.
  Case "leaf".
    unfold insert. remember (insert' k v (bptLeaf b X l)) as insert'. destruct insert'.
    
