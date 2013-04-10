Require Export SfLib.

(* 
 * Proofs about less-than
 *)
Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.
  
Theorem ble_nat_refl : forall n,
    ble_nat n n = true.
Proof.
  induction n. reflexivity.
  simpl. apply IHn.
Qed.
  
Theorem Sn_lt_Sm__n_lt_m : forall n m,
  S n < S m -> n < m.
Proof.
  induction n. intros m H. omega.
  intros m H. destruct m. inversion H. inversion H1. omega.
Qed.

Theorem blt_nat_n_m__blt_nat_Sn_Sm : forall n m,
  blt_nat n m = true -> blt_nat (S n)  (S m) = true.
Proof.
  intros n m H.  destruct m. inversion H.
  unfold blt_nat. unfold blt_nat in H. rewrite <- H. reflexivity.
Qed.

Theorem n_lt_m__Sn_lt_Sm : forall n m,
  n < m -> S n < S m.
Proof.
  intros. induction H; omega.
Qed.
 
Theorem blt_nat_true : forall n m,
  blt_nat n m = true <-> n < m.
Proof. 
  split; generalize dependent m.
  Case "->".
    induction n.  intros m H.
    destruct m. inversion H. omega.
    intros m H. destruct m. inversion H. apply n_lt_m__Sn_lt_Sm. apply IHn. rewrite <- H.
    reflexivity.
  Case "<-".
    induction n. intros m H. destruct m. inversion H. unfold blt_nat. simpl. reflexivity.
    intros m H. destruct m. inversion H. apply Sn_lt_Sm__n_lt_m in H. apply blt_nat_n_m__blt_nat_Sn_Sm.  apply IHn.  apply H.
Qed.
