Require Import HelperFunctions.
Require Import HelperProofs.
Require Import BPlusTree.
Require Import AppearsInKVL.
Require Import SortingProofs.
Require Import BPlusTree.
Require Import ValidBPlusTree.

(* 
 * Proofs about Element at Index 
 *)

Lemma element_at_index_split : forall (X: Type) (b k: nat) (v: X) (l l1 l2: list (nat * X)),
  b = length l1 -> l = l1 ++ (k, v)::l2 -> element_at_index b l = Some (k, v).
Proof.
  intros X b k v.
  induction b.
  Case "b = 0".
    intros.
    symmetry in H. apply length_0_impl_nil in H. subst. simpl.
    reflexivity.
  Case "b = S b".
    intros.
    destruct l1. simpl in H. inversion H.
    destruct l; rewrite <- app_comm_cons in H0; inversion H0.
    simpl.
    simpl in H. inversion H.
    rewrite <- H3. rewrite <- H4.
    apply IHb with (l1 := l1) (l2 := l2); assumption.
Qed.

Lemma element_at_index_app : forall (X: Type) (b k: nat) (v: X) (l1 l2: list (nat * X)),
  b = length l1 -> element_at_index b (l1++(k,v)::l2) = Some (k, v).
Proof.
  intros X b k v.
  induction b.
  Case "b = 0".
    intros.
    symmetry in H. apply length_0_impl_nil in H.
    rewrite H. simpl.
    reflexivity.
  Case "b = S b".
    intros.
    destruct l1; simpl in H; inversion H.
    simpl. rewrite <- H1. apply IHb; assumption.
Qed.

Lemma element_at_index_const : forall (X: Type) (b k: nat) (v: X) (l l1 l2: list (nat * X)),
  b = length l1 -> element_at_index b l = Some (k, v) -> 
  split_list b l = (l1, (k,v)::l2) -> 
  l = l1 ++ (k, v)::l2.
Proof.
  intros X b k v.
  destruct b.
  Case "b = 0".
    intros.
    apply split_list_preserves_lists in H1. inversion H1.
    symmetry in H. apply length_0_impl_nil in H.
    rewrite H. rewrite H in H2. simpl. simpl in H2.
    reflexivity.
  Case "b = S b".
    intros.
    apply split_list_preserves_lists in H1. inversion H1.
    destruct l1; simpl in H; inversion H.
    reflexivity.
Qed.


Lemma element_at_index_cons : forall (X: Type) (b k1 k2: nat) (v1 v2: X) (l: list (nat*X)),
  kvl_sorted ((k1, v1) :: l) ->
  element_at_index b ((k1, v1) :: l) = Some (k2, v2) -> 
  (b = 0 /\ k1 = k2) \/ (b <> 0 /\ k1 < k2).
Proof.
  intros X.
  induction b.
  Case "b = 0".
    intros. left.
    simpl in H0. inversion H0.
    omega.
  Case "b = S b".
    intros. right.
    simpl in H0.
    destruct l.
    SCase "l = []".
      apply element_at_index_impl_appears in H0. inversion H0.
    SCase "l = p::l".
      destruct p.
      inversion H.
      apply blt_nat_true in H7.
      subst.
      apply element_at_index_impl_appears in H0.
      apply appears_in_kvl_app in H0.
      do 3 destruct H0.
      rewrite H0 in H.
      apply kvl_sorted_key_across_app in H.
      omega.
Qed.

Lemma element_at_index_empty_none : forall (X: Type) b,
  @element_at_index X b [] = None.
Proof.
  intros. destruct b; reflexivity.
Qed.
  
Lemma element_at_index_one : forall (X: Type) b (k k1:nat) (v v1: X),
  element_at_index b [(k, v)] = Some (k1, v1) -> k = k1.
Proof. 
  intros. induction b. compute in H. inversion H. reflexivity.
  simpl in H. rewrite element_at_index_empty_none in H. inversion H.
Qed.

Lemma element_at_index_pred_b_implies_left_below_S_b : 
  forall (X: Type) (b k1: nat) (v1: X) (l l1 l2: list (nat*X)),
  b <> 0 ->
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index (pred b) l = Some (k1, v1) ->
  all_keys X (below_equal k1) l1. 
Proof.
  intros. generalize dependent l1. generalize dependent b.
  induction H0; intros.
  Case "kvl_sorted_0".
    apply element_at_index_impl_appears in H3. inversion H3. 
  Case "kvl_sorted_1".
    apply element_at_index_impl_appears in H3. destruct l1. apply ak_empty.
    assert (l2 = []). destruct l1. inversion H1. reflexivity. inversion H1. inversion H3. inversion H1. 
    apply ak_next. symmetry in H9. apply app_eq_nil in H9. destruct H9. rewrite H4. apply ak_empty.
    unfold below_equal. apply ble_nat_symm. inversion H5.
  Case "kvl_sorted_cons". 
    destruct l1. apply ak_empty. destruct l1. destruct p. rewrite <- H4 in H3. subst. simpl in H3.
    apply ak_next. apply ak_empty. inversion H3. inversion H2. rewrite <- H7. rewrite H5. unfold below_equal. apply ble_nat_symm.
    subst. destruct p. apply ak_next.  
     
    apply IHkvl_sorted with (l1:=p0::l1)(b:=length(p0::l1)). 
    simpl. simpl in H3. omega. simpl in H3. simpl. assumption. 
    inversion H2. simpl. reflexivity. reflexivity.
    
    unfold below_equal. assert (k1 >= n1). simpl in H3. destruct (length l1). 
    simpl in H3. inversion H3. apply blt_nat_true in H. omega.
    apply element_at_index_impl_appears in H3. 
    apply appears_in_kvl_app in H3. do 3 destruct H3. destruct witness. inversion H3. apply blt_nat_true in H. omega.
    rewrite H3 in H0. destruct p. inversion H3. subst. apply kvl_sorted_key_across_app in H0. apply blt_nat_true in H. omega.
    apply ble_nat_true. inversion H2. omega.    
Qed.




        

Lemma element_at_index_b_implies_left_below_b : forall (X: Type) (b k1: nat) (v1: X) (l l1 l2: list (nat*X)),
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index b l = Some (k1, v1) ->
  all_keys X (below k1) l1. 
Proof.
  intros.
  generalize dependent l. generalize dependent l1.
  induction b.
  Case "b = 0".
    intros.
    apply length_0_impl_nil in H1.
    subst.
    apply ak_empty.
  Case "b = S b".
    intros.
    destruct l.
    SCase "l = []".
      apply element_at_index_impl_appears in H2.
      inversion H2.
    SCase "l = h :: t".
      simpl in H2.
      destruct l1.
      SSCase "l1 = []".
        apply ak_empty.
      SSCase "l1 = h :: t".
        rewrite <- app_comm_cons in H0.
        inversion H0.
        rewrite <- H4.
        destruct p.
        apply ak_next.
        SSSCase "rest of list below".
          apply IHb with (l := l); try assumption.
            simpl in H1. inversion H1. reflexivity.
            apply list_tail_is_sorted in H. assumption.
        SSSCase "below k1 n".
          unfold below. rewrite blt_nat_true.
          destruct l.
            SSSSCase "l = []".
              apply element_at_index_impl_appears in H2. inversion H2.
            SSSSCase "l = h :: t".
              destruct p.
		      inversion H.
		      destruct b.
		      SSSSSCase "b = 0".
		        simpl in H2.
		        inversion H2.
		        apply blt_nat_true in H11. subst.
		        assumption.
		      SSSSSCase "b = S b".
		        apply element_at_index_cons in H2.
			    inversion H2.
			    inversion H12.
			    inversion H13.
			    inversion H12.
		        apply blt_nat_true in H11. omega.
		        apply list_tail_is_sorted in H.
		        assumption.
Qed.

Lemma element_at_index_b_implies_right_above_b : forall (X: Type) (l l1 l2: list (nat*X)) (b k1: nat) (v1: X),
  kvl_sorted l ->
  l = l1 ++ l2 ->
  length l1 = b ->
  element_at_index b l = Some (k1, v1) ->
  all_keys X (above k1) l2. 
Proof.
  induction l.
  Case "l = []".
    intros.
    symmetry in H0. apply app_eq_nil in H0. inversion H0.
    subst. simpl in *. inversion H2.
  Case "l = a::l".
    intros. destruct a.
    destruct b.
    SCase "b = 0".
      apply length_0_impl_nil in H1. subst.
      simpl in H0. subst.
      simpl in H2. inversion H2. subst.
      apply sorted_all_keys_above_cons.
      apply H.
    SCase "b = S b".
      simpl in H2.
      destruct l1.
      SSCase "l1 = []".
        simpl in H1. inversion H1.
      SSCase "l1 = p::l1".
        rewrite <- app_comm_cons in H0.
        inversion H0.
        simpl in H1. inversion H1.
        eapply IHl.
          apply list_tail_is_sorted in H. apply H.
          apply H5.
          apply H6.
          apply H2.
Qed.

Lemma element_unchanged_by_inserting_greater_key : forall (X: Type) (b k1 k2 k3: nat) (v1 v2 v3: X) (l: list (nat*X)),
  kvl_sorted ((k1, v2)::l) ->
  element_at_index b ((k1, v1) :: l) = Some (k2, v2) ->
  k3 > k2 ->
  element_at_index b ((k1, v1) :: insert_into_list k3 v3 l) = Some (k2, v2).
Proof.
  induction b.
  Case "b = 0".
    intros.
    simpl. simpl in H. inversion H0. reflexivity.
  Case "b = S b".
    intros.
    simpl.
    destruct l.
    simpl in H0. apply element_at_index_impl_appears in H0. inversion H0.
    destruct p.
    assert (kvl_sorted(insert_into_list k3 v3 ((n, x) :: l))).
      apply insert_preserves_sort. apply list_tail_is_sorted in H.
      apply H.
    simpl. simpl in H2.
    remember (ble_nat k3 n) as k3len.
    destruct k3len; symmetry in Heqk3len; [apply ble_nat_true in Heqk3len|apply ble_nat_false in Heqk3len].
    SCase "k3 <= n".
      remember (beq_nat k3 n) as k3eqn.
      destruct k3eqn; symmetry in Heqk3eqn; [apply beq_nat_true_iff in Heqk3eqn|apply beq_nat_false_iff in Heqk3eqn].
      SSCase "k3 = n".
      simpl in H0.
        destruct b.
        simpl in H0. inversion H0.
        subst.
        apply n_lt_n_inversion with (n := k2). apply H1.
        simpl. simpl in H0. apply H0.
      SSCase "k3 < n".
        simpl in H0.
        destruct b.
        SSSCase "b = 0".
          simpl in H0. inversion H0. subst.
          inversion H2.
          apply blt_nat_true in H9.
          apply ex_falso_quodlibet. omega.
        SSSCase "b = S b".
          apply element_at_index_cons in H0. destruct H0.
          inversion H0. inversion H3.
          inversion H0. subst.
          apply ex_falso_quodlibet. omega.
          apply list_tail_is_sorted in H. apply H.	
    SCase "k3 > n".
      simpl in H0.
      apply IHb.
      apply list_tail_is_sorted in H. 
      apply sort_ignores_value with (v1 := x) (v2 := v2) in H.
      apply H.
      apply H0.
      apply H1.
Qed.

Lemma element_changed_by_inserting_equal_key : forall (X: Type) (b k1 k2 k3: nat) (v1 v2 v3: X) (l: list (nat*X)),
  kvl_sorted ((k1, v2)::l) ->
  element_at_index b ((k1, v1) :: l) = Some (k2, v2) ->
  k3 = k2 ->
  exists v4, element_at_index b ((k1, v1) :: insert_into_list k3 v3 l) = Some (k2, v4).
Proof.
  induction b.
  Case "b = 0".
    intros.
    simpl. simpl in H0. exists v2. apply H0.
  Case "b = S b".
    intros.
    simpl. simpl in H0.
    destruct l.
    simpl in H0. apply element_at_index_impl_appears in H0. inversion H0.
    destruct p.
    assert (kvl_sorted(insert_into_list k3 v3 ((n, x) :: l))).
      apply insert_preserves_sort. apply list_tail_is_sorted in H.
      apply H.
    simpl. simpl in H2.
    remember (ble_nat k3 n) as k3len.
    destruct k3len; symmetry in Heqk3len; [apply ble_nat_true in Heqk3len|apply ble_nat_false in Heqk3len].
    SCase "k3 <= n".
      remember (beq_nat k3 n) as k3eqn.
      destruct k3eqn; symmetry in Heqk3eqn; [apply beq_nat_true_iff in Heqk3eqn|apply beq_nat_false_iff in Heqk3eqn].
      SSCase "k3 = n".
        simpl in H0.
        destruct b.
        SSSCase "b = 0".
          simpl in H0. inversion H0.
          subst.
          simpl.
          exists v3. reflexivity.
        SSSCase "b = S b".
          simpl. simpl in H0. rewrite <- H1 in H0.
          exists v2. rewrite <- H1. apply H0.
      SSCase "k3 < n".
        destruct b.
        SSSCase "b = 0".
          simpl. exists v3. rewrite H1. reflexivity.
        SSSCase "b = S b".
          simpl.
          rewrite <- H1 in H0.
          apply element_at_index_cons in H0. destruct H0.
          inversion H0. inversion H3.
          inversion H0. 
          inversion H2. apply blt_nat_true in H11.
          apply ex_falso_quodlibet. omega. 
          apply list_tail_is_sorted in H2. apply H2. 
    SCase "k3 > n".
      eapply IHb.
      apply list_tail_is_sorted in H. 
      apply sort_ignores_value with (v1 := x) (v2:= v2) in H.
      apply H.
      apply H0.
      apply H1.
Qed. 

Lemma element_changed_by_inserting_smaller_key : forall (X: Type) (l: list (nat*X)) (b k2 k3: nat) (v2 v3: X),
  ~ appears_in_kvl k3 l -> 
  kvl_sorted (l) ->
  element_at_index b (l) = Some (k2, v2) ->
  k3 < k2 ->
  element_at_index (S b) (insert_into_list k3 v3 l) = Some (k2, v2).
Proof.
  induction l.
  Case "l = []".
    intros.
    rewrite element_at_index_empty_none in H1. inversion H1.
  Case "l = a::l". destruct a.
    intros. simpl.
    remember (ble_nat k3 n) as k3len.
    destruct k3len; symmetry in Heqk3len; [apply ble_nat_true in Heqk3len|apply ble_nat_false in Heqk3len].
    SSCase "k3 <= n".
      remember (beq_nat k3 n) as k3eqn.
      destruct k3eqn; symmetry in Heqk3eqn; [apply beq_nat_true_iff in Heqk3eqn|apply beq_nat_false_iff in Heqk3eqn].
      SSSCase "k3 = n". subst.
        apply ex_falso_quodlibet. apply H. apply ai_here.
      SSSCase "k3 < n".
        apply H1.
    SSCase "k3 > n".
      destruct b. 
      SSSCase "b = 0". 
        simpl in H1. inversion H1. subst. 
        apply ex_falso_quodlibet. omega.
      SSSCase "b = S b".
       simpl in H1.
       eapply IHl.
         unfold not. intro. apply H. apply ai_later. apply H3.
         apply list_tail_is_sorted in H0. apply H0.
         apply H1.
         apply H2.
Qed.
