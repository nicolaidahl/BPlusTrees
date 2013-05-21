Require Export BPlusTree.
Require Export InductiveDataTypes.
Require Export ValidBPlusTree.


Lemma valid_splits_elim_tail: forall (X: Type) (b k: nat) (kpl': list (nat * bplustree b X)) (subtree: bplustree b X),  
  valid_splits b X (kpl' ++ [(k, subtree)]) ->
  all (above k) (keys subtree).
Proof. 
  intros. 
  induction kpl'.
  Case "kpl' = []".
    simpl in H. inversion H.
    apply H1.
  Case "kpl' = a::kpl'".
    destruct a.
    simpl in H.
    destruct kpl'.
    SCase "kpl' = [a]".
      simpl in H. inversion H. inversion H6.
      apply H8.
    SCase "kpl' = a::p::kpl'".
      destruct p. simpl in H.
      inversion H.
      apply IHkpl'.
      apply H6.
Qed.

Lemma valid_splits_elim_middle: forall (X: Type) (b k1 k2: nat) (kpl' kpl'': list (nat * bplustree b X)) (t1 t2: bplustree b X),  
  valid_splits b X (kpl' ++ (k1, t1)::(k2, t2)::kpl'') ->
  all (between k1 k2) (keys t1).
Proof. 
  intros. 
  induction kpl'.
  Case "kpl' = []".
    simpl in H. inversion H.
    apply H2.
  Case "kpl' = a::kpl'".
    destruct a.
    simpl in H.
    destruct kpl'.
    SCase "kpl' = [a]".
      simpl in H. inversion H. inversion H6.
      apply H9.
    SCase "kpl' = a::p::kpl'".
      destruct p. simpl in H.
      inversion H.
      apply IHkpl'.
      apply H6.
Qed.

Lemma all__keys'_impl_all_keys: forall (X: Type) (b k1 k2: nat) (kvl: list (nat * X)),
  all (between k1 k2) (keys' kvl) -> all_keys X (between k1 k2) kvl.
Proof.
  admit.
Admitted.

