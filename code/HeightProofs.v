Require Export BPlusTree.
Require Export HelperProofs.


(* Proofs about height *)
Lemma height_of_parent_one_bigger: forall (X:Type) b kpl k v l,
  kpl = ((k, v)::l) -> all_values_eq_prop (bplustree b X) (equal_height) kpl ->
  S (height v) = height (bptNode b X kpl).
Proof.
  intros. induction H0; try inversion H; reflexivity.
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