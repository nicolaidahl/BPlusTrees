Require Export bplustree.

Example kvl_sorted_empty : @kvl_sorted nat [].
Proof. apply kvl_sorted_0. Qed.
Example kvl_sorted_single : kvl_sorted [(1, 1)].
Proof. apply kvl_sorted_1. Qed.
Example kvl_sorted_two : kvl_sorted [(1, 1), (2, 2)].
Proof. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. Qed.
Example kvl_sorted_two_WRONG : kvl_sorted [(2, 2), (1, 1)] -> False.
Proof. unfold not. intro. inversion H. inversion H6. Qed.

Lemma sort_ignores_value : forall (X: Type) (k: nat) (v1 v2: X) (l: list (nat * X)),
  kvl_sorted ((k,v1)::l) -> kvl_sorted((k, v2)::l).
Proof.
  intros. inversion H. apply kvl_sorted_1.
  apply kvl_sorted_cons. apply H2. apply H4.
Qed.

Lemma list_tail_is_sorted : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted ((k,v)::l) -> kvl_sorted l.
Proof.
  intros.
  inversion H. apply kvl_sorted_0. apply H2.
Qed.

Lemma list_head_is_sorted : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted (l++[(k,v)]) -> kvl_sorted l.
Proof.
  intros. induction l.
  Case "l = []".
    apply kvl_sorted_0.
  Case "l = a::l".
    destruct a.
    destruct l. 
    SCase "l = []".
      apply kvl_sorted_1.
    SCase "l = a::p::l".
      destruct p.
      repeat rewrite <- app_comm_cons in H.
      inversion H. apply kvl_sorted_cons. apply IHl.
      apply list_tail_is_sorted in H. apply H.
      apply H6.
Qed.

(*
Lemma kvl_sorted_elim_cons : forall (X: Type) (l1 l2: list (nat * X)) (k: nat) (v: X),
  kvl_sorted (l1++((k, v)::l2)) -> kvl_sorted (l1++l2).
Proof.
  intros. induction l2. 
  
  Case "l2 = []".
  simpl. simpl in H. rewrite app_nil_r. apply list_head_is_sorted in H. apply H.
  Case "l2 = a::l2".
    destruct l1. simpl. simpl in H. apply list_tail_is_sorted in H. apply H. 
    destruct l1. simpl. simpl in H.
    inversion H. destruct a. apply kvl_sorted_cons.
    apply list_tail_is_sorted in H2. apply H2.
    subst. inversion H2. subst. apply blt_nat_true.
    apply blt_nat_true in H5. apply blt_nat_true in H8. omega.
   
  
  induction H. 
  Case "kvl_sorted_0".
  symmetry in H1. apply app_eq_nil in H1. inversion H1. inversion H2.
  Case "kvl_sorted_1".
  symmetry in H1. apply app_eq_unit in H1.
  inversion H1; inversion H0. subst. simpl. simpl in H. apply list_tail_is_sorted in H. apply H.
  inversion H3.
  Case "kvl_sorted_cons".
*)  
  
  
  
  
Lemma kvl_sorted_app_elim_l1 : forall (X: Type) (l1 l2: list (nat * X)),
  kvl_sorted (l1++l2) -> kvl_sorted l1 /\ kvl_sorted l2.
Proof.
  intros.
  split.
  Case "kvl_sorted l1".
    induction l1.
    SCase "l1 = []".
      apply kvl_sorted_0.
    SCase "l1 = a::l1".
      rewrite <- app_comm_cons in H.
      destruct l1;  
      destruct a. apply kvl_sorted_1.
      destruct p. inversion H. subst.
      apply kvl_sorted_cons. apply IHl1.
      apply list_tail_is_sorted in H. apply H.
      apply H6.
  Case "kvl_sorted l2".
    induction l2.
    SCase "l2 = []".
      apply kvl_sorted_0.
    SCase "l2 = a::l2".
      admit.
Admitted.
      
  (*
      rewrite <- app_comm_cons in H.
      destruct l1;  
      destruct a. apply kvl_sorted_1.
      destruct p. inversion H. subst.
      apply kvl_sorted_cons. apply IHl1.
      apply list_tail_is_sorted in H. apply H.
      apply H6.
  
  inversion H.
  Case "kvl_sorted_0". 
  symmetry in H1. apply app_eq_nil in H1. inversion H1. subst. apply kvl_sorted_0.
  Case "kvl_sorted_1".
  symmetry in H1. apply app_eq_unit in H1. inversion H1; inversion H0; subst.
  apply kvl_sorted_0. apply kvl_sorted_1.
  Case "kvl_sorted_cons".
  
  
  destruct l1. apply kvl_sorted_0.
  symmetry in H1. apply app_length_le_l1 in H1. simpl in H1. simpl in H1. inversion H1.
  symmetry in H1. apply app_eq_unit in H1.
  inversion H1; inversion H0; subst. apply kvl_sorted_0.
  inversion H0. inversion H4.
  
  symmetry in H1. apply app_eq_nil in H1. inversion H1. subst. apply kvl_sorted_0.
  symmetry in H1. apply app_eq_unit in H1. inversion H1; inversion H0; subst. 
    apply kvl_sorted_0. apply kvl_sorted_1.
  destruct l1. apply kvl_sorted_0. destruct l1. destruct p. apply kvl_sorted_1.
  repeat rewrite <- app_comm_cons in H. inversion H. 
*)  

Lemma split_preserves_sort : forall (X: Type) (l l1 l2: list (nat * X)),
  l1 ++ l2 = l -> kvl_sorted l -> kvl_sorted l1 /\ kvl_sorted l2.
Proof.
  intros. split. 
  induction H0. 
  apply app_eq_nil in H. inversion H. subst. apply kvl_sorted_0.
  apply app_eq_unit in H. inversion H; inversion H0; subst. apply kvl_sorted_0. apply kvl_sorted_1.
  destruct l1. apply kvl_sorted_0. destruct l1. destruct p. apply kvl_sorted_1.
  repeat rewrite <- app_comm_cons in H. inversion H. rewrite H3 in H. rewrite H4 in H.
  apply kvl_sorted_cons. rewrite <- H5 in H0.
 
  

Theorem insert_preserves_sort : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
  kvl_sorted l -> kvl_sorted (insert_into_list k v l).
Proof.
  intros. induction H.
  Case "kvl_sorted_0". simpl. apply kvl_sorted_1.
  Case "kvl_sorted_1". simpl. 
    remember (ble_nat k n) as klen. 
    destruct klen; symmetry in Heqklen; [apply ble_nat_true in Heqklen | apply ble_nat_false in Heqklen].
    SCase "k <= n". remember (beq_nat k n) as keqn. 
      destruct keqn; symmetry in Heqkeqn; [apply beq_nat_true_iff in Heqkeqn | apply beq_nat_false_iff in Heqkeqn].
      SSCase "k = n". apply kvl_sorted_1.
      SSCase "k != n". apply kvl_sorted_cons. apply kvl_sorted_1.
                       apply blt_nat_true. omega.
    SCase "k > n". apply kvl_sorted_cons. apply kvl_sorted_1.
    	apply blt_nat_true. omega.
  Case "kvl_sorted_cons".
    apply blt_nat_true in H0.
    simpl. remember (ble_nat k n1) as klen1.
    destruct klen1; symmetry in Heqklen1; [apply ble_nat_true in Heqklen1 | apply ble_nat_false in Heqklen1].
    SCase "k <= n1". remember (beq_nat k n1) as keqn1.
      destruct keqn1; symmetry in Heqkeqn1; [apply beq_nat_true_iff in Heqkeqn1 | apply beq_nat_false_iff in Heqkeqn1].
      SSCase "k = n1".
        apply kvl_sorted_cons. apply H. apply blt_nat_true. omega.
      SSCase "k != n1".
        apply kvl_sorted_cons. apply kvl_sorted_cons. apply H. apply blt_nat_true. apply H0.
        apply blt_nat_true. omega.
    SCase "k > n1". simpl in IHkvl_sorted. remember (ble_nat k n2) as klen2. 
      destruct klen2; symmetry in Heqklen2; [apply ble_nat_true in Heqklen2 | apply ble_nat_false in Heqklen2].
      SSCase "k <= n2". remember (beq_nat k n2) as keqn2.
        destruct keqn2; symmetry in Heqkeqn2; [apply beq_nat_true_iff in Heqkeqn2 | apply beq_nat_false_iff in Heqkeqn2].
        SSSCase "k = n2".
          apply kvl_sorted_cons. subst.
          eapply sort_ignores_value. apply H.
          apply blt_nat_true. omega.
        SSSCase "k != n2". 
          apply kvl_sorted_cons. apply kvl_sorted_cons. apply H.
          apply blt_nat_true. omega.
          apply blt_nat_true. omega.
     SSCase "k > n2". 
       apply kvl_sorted_cons. apply IHkvl_sorted.
       apply blt_nat_true. omega.
Qed.

Theorem insert_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
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
    

Eval simpl in (split_list' 1 [1, 2] [3, 4, 5]).

Theorem split_list'_preserves_list' : forall (X: Type) (b: nat) (l l1 l2 l3: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list' b l3 l = ((rev l3) ++ l1, l2).
Proof. 
  induction b. 
  Case "b = 0". intros.
    simpl. apply length_0_impl_nil in H. subst. simpl. rewrite app_nil_r. 
    reflexivity.
  Case "b = S b". intros.
    destruct l.
    SCase "l = []".
      apply app_length_le_l1 in H0. simpl in H0. rewrite H in H0. inversion H0.
    SCase "l = x::l".
      simpl. destruct l1. simpl in H. inversion H.
      rewrite <- app_comm_cons in H0. inversion H0. rewrite H3.
      simpl. rewrite rev_app_cons. apply IHb.
      simpl in H. inversion H. reflexivity. apply H3.
Qed.  

Theorem split_list'_preserves_list : forall (X: Type) (b: nat) (l l1 l2: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list' b [] l = (l1, l2).
Proof.
  intros.
  replace (l1) with (rev [] ++ l1) by reflexivity.
  apply split_list'_preserves_list'; assumption.
Qed.

Theorem split_list_preserves_list : forall (X: Type) (b: nat) (l l1 l2: list X),
   length l1 = b -> l1 ++ l2 = l -> split_list b l = (l1, l2).
Proof.
  intros. unfold split_list. apply split_list'_preserves_list; assumption.
Qed.

Theorem insert_preserves_valid_bplustree : forall (b: nat) (X: Type) (t: bplustree b X) (k: nat) (v: X),
  valid_bplustree b X t -> valid_bplustree b X (insert k v t).
Proof.
  intros. induction H. 
  Case "root_is_a_leaf". admit.
  
    (* unfold insert. remember (insert' k v (bptLeaf b X l)) as insert'.
    destruct insert'. inversion Heqinsert'. remember (insert_leaf b k v l) as insert_leaf.
    destruct insert_leaf. destruct o0. remember (head_key l1) as head_key.
    destruct head_key. inversion H3. *)

  Case "valid_root_node". admit.
Admitted.

    