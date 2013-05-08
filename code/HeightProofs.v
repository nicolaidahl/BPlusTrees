Require Export BPlusTree.
Require Export HelperProofs.


(* Proofs about height *)
Lemma height_of_parent_one_bigger: forall (X:Type) b kpl k v l1 l2,
  kpl = (l1 ++ ((k, v)::l2)) -> all_values_eq_prop (bplustree b X) (equal_height) kpl ->
  S (height v) = height (bptNode b X kpl).
Proof.
  intros. induction H0. destruct l1.  inversion H. simpl in H. inversion H. 
  destruct l1. inversion H. simpl. reflexivity. simpl. symmetry in H. apply app_eq_unit in H.
  inversion H. inversion H0. inversion H1. inversion H0. inversion H2.
  admit.
  
Admitted.

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