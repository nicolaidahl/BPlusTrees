Require Export SfLib.
Require Export HelperFunctions.
  
Lemma cut_list_left_add_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  cut_list_left (S b) (x :: l) = x :: cut_list_left b l.
Proof.
  intros X x b. induction b. intros. compute. reflexivity.
  intros. destruct l. reflexivity. simpl. reflexivity.
Qed.


Lemma cut_list_right_remove_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  cut_list_right (S b) (x :: l) = cut_list_right b l.
Proof.
  intros X x b. induction b. intros. reflexivity.
  intros. destruct l. reflexivity.
  simpl. reflexivity.
Qed.
  
Lemma cut_list_add_remove_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  x :: l = x :: (cut_list_left b l ++ cut_list_right b l) ->
  x :: l = cut_list_left (S b) (x :: l) ++ cut_list_right (S b) (x :: l).
Proof.
  intros X x b. induction b; intros.
  Case "b = 0".
    compute. reflexivity.
  Case "b = S b".
   intros. rewrite cut_list_left_add_one. rewrite cut_list_right_remove_one. apply H. 
Qed.

  
Theorem cut_list_left_right_preserves_list : forall (X: Type) (b: nat) (l: list X),
  l = (cut_list_left b l) ++ (cut_list_right b l).
Proof.
  intros X b. induction b. intros. compute. reflexivity.
  intros. destruct l. compute. reflexivity. 
  apply cut_list_add_remove_one. apply cons_remove. apply IHb.
Qed.

  
Theorem split_list_preserves_lists : forall (X: Type) (b: nat) (l l1 l2: list X),
  split_list b l = (l1, l2) -> l = l1 ++ l2.
Proof.
  intros X b. destruct b; intros. 
  Case "b = 0".  
    compute in H. inversion H. reflexivity.
  Case "b = S b".
    unfold split_list in H. destruct l. inversion H. reflexivity.
    rewrite cut_list_right_remove_one in H. rewrite cut_list_left_add_one in H.
    inversion H. rewrite <- app_comm_cons. apply cons_remove. apply cut_list_left_right_preserves_list.
Qed.  
    
(** length **)
Theorem cut_left_length_b: forall {X: Type} b (l: list X),
  length l >= b -> length (cut_list_left b l) = b. 
Proof.
  intros X b. induction b; intros.
  simpl. reflexivity.
  destruct l. 
    inversion H.
    rewrite cut_list_left_add_one. simpl. rewrite IHb; try omega. inversion H; omega.
Qed.
  
    
Theorem split_list_left_length : forall (X: Type) (b: nat) (l l1 l2: list X),
  length l >= b -> split_list b l = (l1, l2) -> length l1 = b.
Proof.
  intros X b. induction b. intros. inversion H0. reflexivity.
  intros. unfold split_list in H0. destruct l. inversion H. 
  simpl in H. rewrite cut_list_left_add_one in H0. inversion H0. simpl. rewrite cut_left_length_b.
  reflexivity. omega.
Qed.
    
Theorem cut_left_not_nil: forall (X: Type) (b: nat) (l: list X),
  length l > 0 -> b <> 0 -> cut_list_left b l <> [].
Proof.
  intros.
  destruct l. simpl in H. apply ex_falso_quodlibet. omega.
  destruct b. apply ex_falso_quodlibet. omega.
  simpl. unfold not. intro. inversion H1.
Qed.

Theorem cut_right_not_nil: forall (X: Type) (b: nat) (l: list X),
  length l > b -> cut_list_right b l <> [].
Proof.
  intros. generalize dependent b.
  induction l. 
  Case "l = []". 
    intros. simpl in H.
    apply ex_falso_quodlibet. omega.
  Case "l = a::l".
    intros.
    destruct b. simpl.  unfold not. intro. inversion H0.
    simpl. apply IHl. simpl in H. omega.
Qed.
  
Lemma cut_list_right_app : forall (X: Type) (b: nat) (l1 l2: list X),
  length l1 >= b -> 
  exists l3, cut_list_right b (l1++l2) = l3++l2.
Proof.
  intros. generalize dependent b.
  induction l1; intros.
  Case "l1 = []".
    assert (b = 0). simpl in H. omega.
    subst. simpl. exists []. reflexivity.
  Case "l1 = a :: l1".
    destruct b. simpl. exists (a::l1). reflexivity.
    simpl. assert (length l1 >= b). inversion H; omega.
    apply IHl1. assumption.
Qed.

Lemma cut_list_left_app : forall (X: Type) (b: nat) (l1 l2: list X),
  length l1 <= b ->
  exists l3, cut_list_left b (l1++l2) = l1++l3.
Proof.
  admit.
Admitted.

Lemma cut_list_left_elim: forall (X: Type) (b1 b2: nat) (l1 l2: list (nat * X)),
  length l1 = b1 ->
  cut_list_left b2 (l1 ++ l2) = l1++cut_list_left (b2 - b1) l2.
Proof.
  (* Informal: We are allowed to move the first b1 items out of cut_list_left,
     as long as we decrease the place to cut with b1 *)
  admit.
Admitted.
  
Lemma cut_list_right_elim: forall (X: Type) (b1 b2: nat) (l1 l2: list (nat * X)),
  length l1 = b1 ->
  cut_list_right b2 (l1 ++ l2) = cut_list_right (b2 - b1) l2.
Proof.
  (* Informal: We can throw the first b1 items out of cut_list_right, as long
     as we decrease the place to cut with b1 *)
  admit.
Admitted.


    
    
    
    
    
    