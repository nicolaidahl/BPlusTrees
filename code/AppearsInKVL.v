Require Export SfLib.
Require Export HelperFunctions.
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

Lemma kv_appears_in_kvl_app : forall (X: Type) (k: nat) (v: X) (l: list (nat*X)),
  kv_appears_in_kvl k v l -> exists l1, exists l2, l = l1++(k,v)::l2.
Proof.
  intros X k v l H. induction H. exists []. exists l. reflexivity.
  inversion IHkv_appears_in_kvl. inversion H0. inversion H1.
  exists ((k0, v0)::witness). exists witness0. 
  simpl. reflexivity.
Qed.

Lemma appears_in_super_set_appears : forall (X: Type) k (x: (nat*X)) (l l': list (nat*X)),
  x :: l' = l -> appears_in_kvl k l' -> appears_in_kvl k l.
Proof.
  intros. generalize dependent l. generalize dependent x. induction H0. intros. 
  rewrite <- H. destruct x. apply aik_later. apply aik_here.
  intros. destruct l0. inversion H. inversion H. destruct p. apply aik_later.
  apply IHappears_in_kvl with (x:= (k0, v)). reflexivity.
Qed.

Lemma kv_appears_in_super_set_appears : forall (X: Type) k v (x: (nat*X)) (l l': list (nat*X)),
  x :: l' = l -> kv_appears_in_kvl k v l' -> kv_appears_in_kvl k v l.
Proof.
  intros. generalize dependent l. generalize dependent x. induction H0. intros. 
  rewrite <- H. destruct x. apply kv_aik_later. apply kv_aik_here.
  intros. destruct l0. inversion H. inversion H. destruct p. apply kv_aik_later.
  apply IHkv_appears_in_kvl with (x:= (k0, v0)). reflexivity.
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

Lemma kv_appears_in_kvl_dist_app : forall (X: Type) (k: nat) (v: X) (l l1 l2: list (nat*X)),
  l = l1++l2 -> kv_appears_in_kvl k v l -> 
  kv_appears_in_kvl k v l1 \/ kv_appears_in_kvl k v l2.
Proof.
  intros. generalize dependent l1. induction H0; intros.
  Case "kv_aik_here".
    destruct l1. destruct l2; inversion H. destruct p. 
    inversion H1. right. apply kv_aik_here.
    destruct p. inversion H. left. apply kv_aik_here.
  Case "kv_aik_later".
    destruct l1. simpl in H. right. eapply kv_appears_in_super_set_appears. apply H. assumption.
    inversion H. 
      assert(
        kv_appears_in_kvl k v l1 \/ kv_appears_in_kvl k v l2 ->
        kv_appears_in_kvl k v ((k0, v0) :: l1) \/ kv_appears_in_kvl k v l2). 
        intros. destruct H1. left. apply kv_aik_later. assumption. right. assumption. 
    apply H1. apply IHkv_appears_in_kvl. apply H3.
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

Lemma kv_appears_cons : forall (X: Type) (k k1: nat) (v v1: X) (l: list (nat*X)),
  kv_appears_in_kvl k v ((k1, v1) :: l) -> 
  k <> k1 -> 
  kv_appears_in_kvl k v (l).
Proof.
  intros.
  inversion H.
  subst.
  apply ex_falso_quodlibet. omega.
  subst.
  apply H2.
Qed.


Theorem insert_into_list_appears : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kv_appears_in_kvl k v (insert_into_list k v l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. apply kv_aik_here.
  Case "l = a::l".
    destruct a. simpl. 
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n".
        apply kv_aik_here.
      SSCase "k <> n".
      apply kv_aik_here.
    SCase "k > n".
      apply kv_aik_later. apply IHl.
Qed.



Lemma key_greater_than_all_keys_does_not_appear : forall (X: Type) (k kb: nat) (l: list (nat*X)), 
  kvl_sorted l ->
  all_keys X (below kb) l ->
  k >= kb ->

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

Lemma appears_in_kvl_cons_middle: forall (X: Type) k n x (l1 l2: list (nat * X)),
  appears_in_kvl k (l1 ++ l2) ->
  appears_in_kvl k (l1 ++ (n, x) :: l2).
Proof.
  intros. induction l1. destruct l2. inversion H. 
  destruct p. simpl in H. simpl. apply aik_later. apply H.
  destruct a.
  remember (beq_nat k n0).  destruct b.
  symmetry in Heqb. apply beq_nat_true_iff in Heqb. subst.
  apply aik_here.
  simpl.
  apply aik_later. apply IHl1.
  simpl in H.
  apply appears_cons in H. assumption. apply beq_nat_false_iff. symmetry. assumption.
Qed.
  
Lemma not_appears_in_kvl_impl_remove_element: forall (X: Type) n x k (l1 l2: list (nat * X)),
  ~ appears_in_kvl k (l1 ++ (n, x) :: l2) ->
  ~ appears_in_kvl k (l1 ++ l2).
Proof.
  intros. unfold not in H. unfold not. intro.
  eapply appears_in_kvl_cons_middle in H0. apply H in H0. assumption.
Qed.


Lemma not_appears_in_kvl_key_not_equal: forall (X: Type) n x k (l1 l2: list (nat * X)),
  ~ appears_in_kvl k (l1 ++ (n, x) :: l2) ->
  k <> n.
Proof.
  intros. unfold not. unfold not in H. intro. apply H.
  induction l1; simpl; subst. 
  Case "l1 = []".
    apply aik_here.
  Case "l1 = a :: l1".
    destruct a. 
      apply aik_later. 
      simpl in H.
      apply IHl1. intro. apply H.
      apply aik_later. assumption.
Qed.

Lemma insert_into_list_eq_nil_impl_false: forall (X: Type) b k1 v1 (l: list (nat * bplustree b X)),
  [] = insert_into_list k1 v1 l -> False.
Proof.
  intros.
  induction l.
    inversion H.
    apply IHl. 
    simpl in H.
    destruct a.
    remember (ble_nat k1 n).
    destruct b1; symmetry in Heqb1; [apply ble_nat_true in Heqb1 | apply ble_nat_false in Heqb1].
      remember (beq_nat k1 n).
      destruct b1; symmetry in Heqb0; [apply beq_nat_true in Heqb0 | apply beq_nat_false in Heqb0]; inversion H.
      inversion H.
Qed.

Lemma cut_list_left_ins_ins_two_crazy: forall (X: Type) b (kpl' left: list (nat* bplustree b X))
                                       n4 b5 b3 n2 b2 n1,
  b <> 0 ->
  appears_in_kvl n1 ((n4, b5) :: kpl') ->
  left = cut_list_left (S b) (insert_into_list n1 b2 (insert_into_list n2 b3 ((n4, b5) :: kpl'))) ->
  kvl_sorted ((n4, b5) :: kpl') ->
  appears_in_kvl n4 left.
Proof.
  intros.
  destruct b.
  Case "b = 0".
    exfalso. omega. 
  Case "b = S b".
    apply appears_in_kvl_app in H0. do 3 destruct H0.
    destruct witness.
    SCase "witness = []".
      inversion H0.
      subst.
      simpl.
      remember (ble_nat n2 n1).
      destruct b0; symmetry in Heqb0; [apply ble_nat_true in Heqb0 | apply ble_nat_false in Heqb0].
      SSCase "n2 <= n1".
        remember (beq_nat n2 n1).
        destruct b0; symmetry in Heqb1; [apply beq_nat_true in Heqb1 | apply beq_nat_false in Heqb1].
        SSSCase "n2 = n1".
          remember (insert_into_list n1 b2 ((n2, b3) :: witness0)).
          destruct l.
          SSSSCase "l = []".
            apply insert_into_list_eq_nil_impl_false in Heql. exfalso. assumption.
          SSSSCase "l = p :: l".
            simpl in Heql.
            assert (beq_nat n1 n2 = true). 
              apply beq_nat_true_iff in Heqb1. rewrite beq_nat_sym in Heqb1. assumption.
            rewrite H1 in Heql.
            remember (ble_nat n1 n2).
            destruct  b0; symmetry in Heqb2; [apply ble_nat_true in Heqb2 | apply ble_nat_false in Heqb2]. 
              SSSSSCase "n1 <= n2".
                inversion Heql.
                destruct witness0.
                SSSSSSCase "witness0 = []".
                  constructor.
                SSSSSSCase "witness0 = [p :: witness0]".
                  subst. constructor.
              SSSSSCase "~n1 <= n2".
                inversion Heql.
                remember (insert_into_list n1 b2 witness0).
                destruct l0.
                SSSSSSCase "l0 = []".
                  apply insert_into_list_eq_nil_impl_false in Heql0. exfalso. assumption.
                SSSSSSCase "l0 = p :: l0".
                  subst. constructor.
        SSSCase "n2 <> n1".
          inversion Heqb0. exfalso. omega.
          remember (insert_into_list (S m) b2 ((n2, b3) :: (S m, witness1) :: witness0)).
          destruct l.
          SSSSCase "l = []".
            apply insert_into_list_eq_nil_impl_false in Heql. exfalso. assumption.
          SSSSCase "l = p :: l".
            simpl in Heql.
            subst.
            destruct n2.
            SSSSSCase "n2 = 0".
              remember (ble_nat m m).
              destruct b0; symmetry in Heqb2; [apply ble_nat_true in Heqb2 | apply ble_nat_false in Heqb2].
              SSSSSSCase "m <= m".
                remember (beq_nat m m).
                destruct b0; symmetry in Heqb3; [apply beq_nat_true in Heqb3 | apply beq_nat_false in Heqb3].
                  SSSSSSSCase "m = m".
                    inversion Heql.
                    repeat constructor.
                  SSSSSSSCase "m <> m".
                    exfalso. omega.
              SSSSSSCase "~m<=m".
                exfalso. omega.
            SSSSSCase "n2 = S n2".
              remember (ble_nat m n2).
              destruct b0; symmetry in Heqb2; [apply ble_nat_true in Heqb2 | apply ble_nat_false in Heqb2].
              SSSSSSCase "m <= n2".
                remember (beq_nat m n2).
                destruct b0; symmetry in Heqb3; [apply beq_nat_true in Heqb3 | apply beq_nat_false in Heqb3]; 
                  inversion Heql; constructor.
              SSSSSSCase "~m <= n2".
                remember (ble_nat m m).
                destruct b0; symmetry in Heqb3; [apply ble_nat_true in Heqb3 | apply ble_nat_false in Heqb3].
                SSSSSSSCase "m <= m".
                  remember (beq_nat m m).
                  destruct b0; symmetry in Heqb4; [apply beq_nat_true in Heqb4 | apply beq_nat_false in Heqb4];
                    inversion Heql; repeat constructor.
                SSSSSSSCase "~m <= m".
                  inversion Heql.
                  repeat constructor.
      SSCase "~n2 <= n1".
        simpl.
        remember (ble_nat n1 n1).
        destruct b0; symmetry in Heqb1; [apply ble_nat_true in Heqb1 | apply ble_nat_false in Heqb1].
        SSSCase "n1 <= n1".
          remember (beq_nat n1 n1).
          destruct b0; symmetry in Heqb2; [apply beq_nat_true in Heqb2 | apply beq_nat_false in Heqb2].
          SSSSCase "n1 = n1".
            remember (insert_into_list n2 b3 witness0).
            destruct l.
            SSSSSCase "l = []".
              apply insert_into_list_eq_nil_impl_false in Heql. exfalso. assumption. 
            SSSSSCase "l = p :: l".
              constructor.
          SSSSCase "n1 <> n1".
            exfalso. omega.
        SSSCase "~ n1 <= n1". 
          exfalso. omega. 
    SCase "witness = p :: witness".
      inversion H0.
      subst.
      simpl.
      remember (ble_nat n2 n4).
      destruct b0; symmetry in Heqb0; [apply ble_nat_true in Heqb0 | apply ble_nat_false in Heqb0].
      SSCase "n2 <= n4".
        remember (beq_nat n2 n4).
        destruct b0; symmetry in Heqb1; [apply beq_nat_true in Heqb1 | apply beq_nat_false in Heqb1].
        SSSCase "n2 = n4".
          remember (insert_into_list n1 b2 ((n2, b3) :: witness ++ (n1, witness1) :: witness0)).
          destruct l.
          SSSSCase "l = []".
            apply insert_into_list_eq_nil_impl_false in Heql. exfalso. assumption. 
          SSSSCase "l = p :: l".
            simpl in Heql.
            remember (ble_nat n1 n2).
            destruct b0; symmetry in Heqb2; [apply ble_nat_true in Heqb2 | apply ble_nat_false in Heqb2].
            SSSSSCase "n1 <= n2".
              remember (beq_nat n1 n2).
              destruct b0; symmetry in Heqb3; [apply beq_nat_true in Heqb3 | apply beq_nat_false in Heqb3].
                SSSSSSCase "n1 = n2".
                  inversion Heql.
                  remember (witness ++ (n1, witness1) :: witness0).
                    destruct l0.
                    SSSSSSSCase "l0 = []".
                      subst. constructor.
                    SSSSSSSCase "l0 = p :: l0".
                      subst. constructor.
                SSSSSSCase "n1 <> n2".
                  inversion Heql. subst. repeat constructor.
            SSSSSCase "~n1 <= n2".
              inversion Heql.
              remember (insert_into_list n1 b2 (witness ++ (n1, witness1) :: witness0)).
              destruct l0.
              SSSSSSCase "l0 = []".
                apply insert_into_list_eq_nil_impl_false in Heql0. exfalso. omega.
              SSSSSSCase "l0 = p :: l0".
                subst. constructor.
        SSSCase "n2 <> n4".
          remember (insert_into_list n1 b2 ((n2, b3) :: (n4, b5) :: witness ++ (n1, witness1) :: witness0)).
          destruct l.
          SSSSCase "l = []".
            apply insert_into_list_eq_nil_impl_false in Heql. exfalso. assumption. 
          SSSSCase "l = p :: l".
            simpl in Heql.
            remember (ble_nat n1 n2).
            destruct b0; symmetry in Heqb2; [apply ble_nat_true in Heqb2 | apply ble_nat_false in Heqb2].
            SSSSSCase "n1 <= n2".
              remember (beq_nat n1 n2).
              destruct b0; symmetry in Heqb3; [apply beq_nat_true in Heqb3 | apply beq_nat_false in Heqb3].
              SSSSSSCase "n1 = n2".
                inversion Heql. subst. repeat constructor.
              SSSSSSCase "n1 <> n2".
                inversion Heql. subst. repeat constructor.
                apply kvl_sorted_key_across_app in H2. exfalso. omega.
            SSSSSCase "~n1 <= n2".
              remember (ble_nat n1 n4).
              destruct b0; symmetry in Heqb3; [apply ble_nat_true in Heqb3 | apply ble_nat_false in Heqb3].
              SSSSSSCase "n1 <= n4".
                remember (beq_nat n1 n4).
                destruct b0; symmetry in Heqb4; [apply beq_nat_true in Heqb4 | apply beq_nat_false in Heqb4].
                  apply kvl_sorted_key_across_app in H2. exfalso. omega.
                  apply kvl_sorted_key_across_app in H2. exfalso. omega.
              SSSSSSCase "~n1 <= n4".
                inversion Heql.
                repeat constructor.
      SSCase "~n2 <= n4".
        remember (insert_into_list n1 b2 ((n4, b5) :: insert_into_list n2 b3 (witness ++ (n1, witness1) :: witness0))).
        destruct l.
        SSSCase "l = []".
          apply insert_into_list_eq_nil_impl_false in Heql. exfalso. omega.
        SSSCase "l = p :: l".
          inversion Heql.
          remember (ble_nat n1 n4).
          destruct b0; symmetry in Heqb1; [apply ble_nat_true in Heqb1 | apply ble_nat_false in Heqb1].
          SSSSCase "n1 <= n4".
            remember (beq_nat n1 n4).
            destruct b0; symmetry in Heqb2; [apply beq_nat_true in Heqb2 | apply beq_nat_false in Heqb2].
            SSSSSCase "n1 = n4".
              remember (insert_into_list n2 b3 (witness ++ (n1, witness1) :: witness0)).
              destruct l0.
                SSSSSSCase "l0 = []".
                  subst.
                  apply insert_into_list_eq_nil_impl_false in Heql0. exfalso. assumption.
                SSSSSSCase "l0 = p :: l0".
                  apply kvl_sorted_key_across_app in H2. exfalso. omega. 
            SSSSSCase "n1 <> n4".
              inversion H3.
              subst. repeat constructor.
          SSSSCase "~n1 <= n4".
            inversion H3.
            remember (insert_into_list n1 b2 (insert_into_list n2 b3 (witness ++ (n1, witness1) :: witness0))).
            destruct l0.
            SSSSSCase "l0 = []".
              apply insert_into_list_eq_nil_impl_false in Heql0. exfalso. assumption.
            SSSSSCase "l0 = p :: l0".
              repeat constructor.
Qed.
