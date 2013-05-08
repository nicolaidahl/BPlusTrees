Require Export BPlusTree.
Require Export HelperProofs.


(* Proofs about height *)
Lemma eq_height_subtrees_removes_cons: forall {X:Type} b x1 x2 n1 n2 l,
  equal_height x1 x2 ->
  height (bptNode b X ((n1, x1) :: (n2, x2) :: l)) = height (bptNode b X ((n2, x2) :: l)).
Proof. 
  intros. simpl. unfold equal_height in H. apply beq_nat_true in H. omega.
Qed.

Lemma height_of_parent_one_bigger_first: forall (X:Type) b k v l, 
  all_values_eq_prop (bplustree b X) (equal_height) ((k, v)::l) ->
  S (height v) = height (bptNode b X ((k, v)::l)).
Proof.
  intros; inversion H; simpl; reflexivity.
Qed.

Lemma height_of_parent_one_bigger: forall (X:Type) b kpl k v l1 l2,
  kpl = (l1 ++ ((k, v)::l2)) -> all_values_eq_prop (bplustree b X) (equal_height) kpl ->
  S (height v) = height (bptNode b X kpl).
Proof.
  intros. generalize dependent l1. induction H0; intros. destruct l1. inversion H. 
  simpl in H. inversion H. destruct l1. inversion H. simpl. reflexivity. simpl. 
  symmetry in H. apply app_eq_unit in H. inversion H. inversion H0. inversion H1. 
  inversion H0. inversion H2.
  Case "Induction case".
    rewrite eq_height_subtrees_removes_cons. destruct l1. inversion H1. destruct l2. inversion H5.
    destruct p. subst. simpl in H1. unfold equal_height in H. apply beq_nat_true in H.
    rewrite H. apply height_of_parent_one_bigger_first. assumption.
    
    destruct p. inversion H1.
     apply IHall_values_eq_prop with (l1:=l1). assumption. assumption.
Qed.


Lemma height_cons: forall (X: Type) (b k: nat) (p: bplustree b X) (l: list (nat * bplustree b X)),
  valid_bplustree b X (bptNode b X ((k, p)::l)) ->
  valid_bplustree b X (bptNode b X (l)) ->
  ((height (bptNode b X ((k, p)::l)))) = ((height (bptNode b X (l)))).
Proof.
  intros.
  inversion H.
  inversion H6. 
    inversion H0.
    subst.
    simpl in H14. apply ex_falso_quodlibet. omega.
    simpl. 
    unfold equal_height in H13.
    rewrite beq_nat_true_iff in H13. omega.
Qed.