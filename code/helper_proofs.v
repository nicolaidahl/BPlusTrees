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

Theorem blt_nat_n_m_false__blt_nat_Sn_Sm : forall n m,
  blt_nat n m = false -> blt_nat (S n)  (S m) = false.
Proof.
  intros n m H.  destruct m. unfold blt_nat. simpl. reflexivity.
  unfold blt_nat. simpl. unfold blt_nat in H. simpl in H. apply H.
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

Theorem blt_nat_false : forall n m,
  blt_nat n m = false <-> ~(n < m).
Proof. 
  split; generalize dependent m.
  Case "->".
    unfold not. intros. unfold blt_nat in H. apply ble_nat_false in H. omega.
  Case "<-".
    induction n. 
    SCase "n = 0". 
      intros. destruct m. unfold blt_nat. simpl. reflexivity.
      unfold not in H. apply ex_falso_quodlibet. apply H. omega.
    SCase "n = S n".
      intros. destruct m. compute. reflexivity.
      apply blt_nat_n_m_false__blt_nat_Sn_Sm.
      apply IHn.
      unfold not. unfold not in H.
      intro. apply H. 
      apply n_lt_m__Sn_lt_Sm. apply H0.
Qed.

(*
 * Proofs about max
 *)
Definition max_nat (n1 n2 : nat) : nat :=
  if ble_nat n1 n2
  then n2
  else n1.
  
Example max_nat_1 : max_nat 1 5 = 5.
Proof. simpl. reflexivity. Qed.
Example max_nat_2 : max_nat 11 3 = 11.
Proof. simpl. reflexivity. Qed.
Example max_nat_3 : max_nat 2 2 = 2.
Proof. simpl. reflexivity. Qed.
  