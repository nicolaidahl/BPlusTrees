Require Export ValidBPlusTree.
Require Export SfLib.
Require Export HelperProofs.
Require Export BPlusTree.

 

Theorem deletion_first_in_kvl: forall (X: Type) (sk:nat) (v : X) (l l': list (nat * X)),
  l = (sk, v) :: l' -> delete_from_list sk l = l'.
Proof.
  intros X sk v l l'. intro H.
  unfold delete_from_list. induction l. inversion H.
  destruct a. remember (beq_nat n sk) as beqnsk. destruct beqnsk. 
  inversion H. reflexivity. 
  inversion H. symmetry in Heqbeqnsk. rewrite -> beq_nat_false_iff in Heqbeqnsk. 
  unfold not in Heqbeqnsk. apply Heqbeqnsk in H1. inversion H1.
Qed.

Theorem delete_not_first: forall (X: Type) (sk n:nat) (v : X) (l: list (nat * X)),
  sk <> n -> delete_from_list sk ((n, v) :: l) = (n, v) :: (delete_from_list sk l).
Proof.
  Admitted. 
  
Lemma blt_implies_not_eq: forall (n1 n2: nat),
  blt_nat n1 n2 = true -> beq_nat n1 n2 = false.
Proof.
  intros n1 n2 H. apply blt_nat_true in H. apply beq_nat_false_iff. omega.
Qed.

Theorem delete_any_in_kvl: forall (X: Type) (sk:nat) (v : X) (l ls le: list (nat * X)),
  kvl_sorted l -> ls ++ ((sk, v) :: le) = l -> delete_from_list sk l = ls ++ le.
Proof.
  intros X sk v l ls le Hsort H. induction Hsort.
  Case "kvl_sorted_0".
    simpl. apply app_eq_nil in H. inversion H. inversion H1.
  Case "kvl_sorted_1".
	simpl. remember (beq_nat n sk) as beqnsk. destruct beqnsk. 
	    SCase "beq_nat n sk = true".
	      apply app_eq_unit in H. inversion H.
	      inversion H0. inversion H2. rewrite H1. reflexivity. inversion H0. inversion H2.
	    SCase "beq_nat n sk = false".
	      apply app_eq_unit in H. inversion H. inversion H0. inversion H2. 
	      symmetry in Heqbeqnsk. apply beq_nat_false_iff in Heqbeqnsk. rewrite H4 in Heqbeqnsk.
	      unfold not in Heqbeqnsk. apply ex_falso_quodlibet. apply Heqbeqnsk. reflexivity.
	      inversion H0. inversion H2.
  Case "kvl_sorted_cons".
    destruct ls. simpl. remember (beq_nat n1 sk) as beqn1sk. destruct beqn1sk.
    SCase "beq_nat n1 sk = true".
      inversion H. reflexivity.
    SCase "beq_nat n1 sk = false".
      inversion H. assert (beq_nat n2 n1 = false). apply blt_implies_not_eq in H0. 
      rewrite beq_nat_sym. apply H0. rewrite H1.
      admit. admit.
      
Admitted.
  
  

Theorem deletion_in_list_removes_element: forall (X: Type) (sk: nat) (l: list (nat * X)),
  search_leaf sk (delete_from_list sk l) = None.
Proof.
  intros X sk l. 
  
  
  
   remember (delete_from_list sk l) as del.
  induction del. reflexivity.
  unfold search_leaf.
  admit.
  Admitted.
(*
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
Admitted.*)