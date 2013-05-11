Require Export HelperFunctions.
Require Export LowLevelHelperProofs.
Require Export HelperProofs.
Require Export BPlusTree.
Require Export InductiveDataTypes.
Require Export SortingProofs.

(* 
 * Proofs about appears In List 
 *)
Lemma element_at_index_impl_appears: forall (X: Type) (b k: nat) (v: X) (l: list (nat*X)),
  element_at_index b l = Some (k, v) -> appears_in_kvl k l.
Proof.
  intro X. induction b; intros; destruct l; inversion H; destruct p.
  Case "b = 0".
     inversion H. apply aik_here.
  Case "b = S b".
    apply aik_later. apply IHb with (v:=v). inversion H. reflexivity.
Qed.

Lemma appears_in_kvl_app : forall (X: Type) (k: nat) (l: list (nat*X)),
  appears_in_kvl k l -> exists l1, exists l2, exists v, l = l1++(k,v)::l2.
Proof.
  intros X k l H. induction H. exists []. exists l. exists v. reflexivity.
  inversion IHappears_in_kvl. inversion H0. inversion H1.
  exists ((k0, v)::witness). exists witness0. exists witness1. simpl. rewrite cons_remove. apply H2.
Qed.

Lemma appears_in_super_set_appears : forall (X: Type) k (x: (nat*X)) (l l': list (nat*X)),
  x :: l' = l -> appears_in_kvl k l' -> appears_in_kvl k l.
Proof.
  intros. generalize dependent l. generalize dependent x. induction H0. intros. 
  rewrite <- H. destruct x. apply aik_later. apply aik_here.
  intros. destruct l0. inversion H. inversion H. destruct p. apply aik_later.
  apply IHappears_in_kvl with (x:= (k0, v)). reflexivity.
Qed.



Lemma appears_in_kvl_dist_app : forall (X: Type) (k: nat) (l l1 l2: list (nat*X)),
  l = l1++l2 -> appears_in_kvl k l -> 
  appears_in_kvl k l1 \/ appears_in_kvl k l2.
Proof.
  intros. generalize dependent l1. induction H0; intros.
  Case "aik_here".
    destruct l1. destruct l2; inversion H. destruct p. simpl in H1.
    inversion H1. right. apply aik_here.
    destruct p. inversion H. left. apply aik_here.
  Case "aik_later".
    destruct l1. simpl in H. right. eapply appears_in_super_set_appears. apply H. assumption.
    inversion H. 
      assert(
        appears_in_kvl k l1 \/ appears_in_kvl k l2 ->
        appears_in_kvl k ((k0, v) :: l1) \/ appears_in_kvl k l2). 
        intros. destruct H1. left. apply aik_later. assumption. right. assumption. 
    apply H1. apply IHappears_in_kvl. apply H3.
Qed.

Theorem appears_kvl_appears_leaf_tree: forall {X: Type} (b: nat) k l,
  appears_in_kvl k l -> appears_in_tree k (bptLeaf b X l).
Proof.
  intros. induction H. apply ait_leaf. apply aik_here. apply ait_leaf.
  eapply appears_in_super_set_appears. reflexivity. apply H.
Qed.

Lemma appears_cons : forall (X: Type) (k k1: nat) (v1: X) (l: list (nat*X)),
  appears_in_kvl k ((k1, v1) :: l) -> 
  k <> k1 -> 
  appears_in_kvl k (l).
Proof.
  intros.
  inversion H.
  subst.
  apply ex_falso_quodlibet. omega.
  subst.
  apply H2.
Qed.

Theorem insert_into_list_appears : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  appears_in_kvl k (insert_into_list k v l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. apply aik_here.
  Case "l = a::l".
    destruct a. simpl. 
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        apply aik_here.
      SSCase "k <> n".
      apply aik_here.
    SCase "k > n".
      apply aik_later. apply IHl.
Qed.



Lemma key_greater_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below kb) l ->
  k > kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst. 
  inversion H3. apply blt_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.

Lemma key_greater_than_all_keys_does_not_appear_ble : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below_equal kb) l ->
  k > kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst. 
  inversion H3. apply ble_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.

Lemma key_smaller_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (above kb) l ->
  k < kb ->

  ~ appears_in_kvl k l.
Proof.
  unfold not.
  intros.
  induction H0.
  subst. inversion H2.
  apply IHall_keys.
  apply list_tail_is_sorted in H. apply H.
  remember (beq_nat k n).
  destruct b; symmetry in Heqb; [apply beq_nat_true_iff in Heqb|apply beq_nat_false_iff in Heqb].
  subst.
  inversion H3. apply ble_nat_true in H5. apply ex_falso_quodlibet. omega.
  apply appears_cons in H2. assumption.
  assumption.
Qed.


