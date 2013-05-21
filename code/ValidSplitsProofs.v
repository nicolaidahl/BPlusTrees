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

Lemma insert_into_list_preserves_all__keys': forall (X: Type) (k1 k2 k: nat) (v: X) (l: list (nat * X)),
  all (between k1 k2) (keys' l) ->
  between k1 k2 k ->
  
  all (between k1 k2) (keys' (insert_into_list k v l)).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. repeat constructor. apply H0.
  Case "l = a::l".
    destruct a.
    destruct l.
    SCase "l = [a]".
      simpl.
      remember (ble_nat k n) as klen.
      destruct klen; symmetry in Heqklen; [ apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen ].
      SSCase "k <= n".
        remember (beq_nat k n) as keqn.
        destruct keqn; symmetry in Heqkeqn; [ apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn ].
        SSSCase "k = n".
          repeat constructor. apply H0.
        SSSCase "k < n".
          constructor. simpl in H. apply H. apply H0.
      SSCase "k > n".
        inversion H. repeat constructor; assumption.
    SCase "l = a::p::l".
      destruct p.
      simpl.
      remember (ble_nat k n) as klen.
      destruct klen; symmetry in Heqklen; [ apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen ].
      SSCase "k <= n".
        remember (beq_nat k n) as keqn.
        destruct keqn; symmetry in Heqkeqn; [ apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn ].
        SSSCase "k = n".
          simpl. simpl in H.
          constructor. inversion H. apply H3. apply H0.
        SSSCase "k < n".
          simpl. simpl in H.
          constructor. apply H. apply H0.
      SSCase "k > n".
        simpl in IHl.
        remember (ble_nat k n0) as klen0.
        destruct klen0; symmetry in Heqklen0; [ apply ble_nat_true in Heqklen0 | apply ble_nat_false in Heqklen0 ].
        SSSCase "k <= n0".
          remember (beq_nat k n0) as keqn0.
          destruct keqn0; symmetry in Heqkeqn0; [ apply beq_nat_true_iff in Heqkeqn0 | apply beq_nat_false_iff in Heqkeqn0 ].
          SSSSCase "k = n0".
            simpl. simpl in H. 
            inversion H. 
            constructor; try assumption.
            constructor; try assumption.
            inversion H3. assumption.
          SSSSCase "k < n0".
            simpl. simpl in H.
            inversion H.
            constructor; try assumption.
            constructor; try assumption.
        SSSCase "k > n0".
          simpl. simpl in IHl.
          constructor. apply IHl.
          simpl in H. inversion H. assumption.
          simpl in H. inversion H. assumption.
Qed.

Lemma all__keys'_impl_all_keys: forall (X: Type) (b k1 k2: nat) (kvl: list (nat * X)),
  all (between k1 k2) (keys' kvl) -> all_keys X (between k1 k2) kvl.
Proof.
  admit.
Admitted.

