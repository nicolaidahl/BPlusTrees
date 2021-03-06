Require Export SfLib.
Require Export HelperFunctions.
Require Export InductiveDataTypes.
  
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
  intros. generalize dependent l1.
  induction b; intros.
  Case "b = 0".
    simpl.
    exists [].
    apply length_gt_0_impl_nil in H. subst. reflexivity.
  Case "b = S b".
    destruct l1.
    SCase "l1 = []".
      destruct l2. 
      SSCase "l2 = []". 
        simpl. exists []. reflexivity.
      SSCase "l2 = x :: l2".
        simpl. exists (x :: cut_list_left b l2). reflexivity.
    SCase "l1 = x :: l1".
      rewrite <- app_comm_cons. simpl. simpl in H. 
      assert ((exists l3 : list X, cut_list_left b (l1 ++ l2) = l1 ++ l3) -> 
              (exists l3 : list X, x :: cut_list_left b (l1 ++ l2) = x :: l1 ++ l3)).
        intros. destruct H0. 
        exists witness. apply cons_remove. apply H0.
      apply H0. apply IHb. omega.
Qed.

Lemma cut_list_left_elim: forall (X: Type) (b1 b2: nat) (l1 l2: list (nat * X)),
  length l1 = b1 -> b1 <= b2 -> b2 <= length l2 ->
  cut_list_left b2 (l1 ++ l2) = l1++cut_list_left (b2 - b1) l2.
Proof.
  (* Informal: We are allowed to move the first b1 items out of cut_list_left,
     as long as we decrease the place to cut with b1 *)
  intros. generalize dependent b1. generalize dependent l1. generalize dependent l2.
  induction b2; intros.
  Case "b2 = 0".
    inversion H0.
    simpl. subst. apply length_0_impl_nil in H2. subst. reflexivity.
  Case "b2 = S b2".
    destruct l1.
      SCase "l1 = []".
        destruct l2; simpl in H; rewrite <- H; rewrite <- minus_n_O; simpl; reflexivity.
      SCase "l1 = a :: l1".
        destruct l2.
        SSCase "l2 = []".
          simpl in H1. assert (S b2 = 0) by omega. assert (b1 = 0) by omega.
          rewrite H2. rewrite H3. simpl. subst. apply length_0_impl_nil in H3.
          inversion H3.
        SSCase "l2 = p0 :: l2".
          destruct b1.
          SSSCase "b1 = 0".
            simpl. inversion H.
          SSSCase "b1 = S b1".
            replace (S b2 - S b1) with (b2 - b1) by omega.
            rewrite <- app_comm_cons. simpl. simpl in H. apply cons_remove. apply IHb2; omega.
Qed.
  
Lemma cut_list_right_elim: forall (X: Type) (b1 b2: nat) (l1 l2: list (nat * X)),
  length l1 = b1 -> b1 <= b2 -> b2 <= length l2 ->
  cut_list_right b2 (l1 ++ l2) = cut_list_right (b2 - b1) l2.
Proof.
  (* Informal: We can throw the first b1 items out of cut_list_right, as long
     as we decrease the place to cut with b1 *)
  intros. generalize dependent b1. generalize dependent l1. generalize dependent l2.
  induction b2; intros.
  Case "b2 = 0".
    inversion H0.
    simpl. subst. apply length_0_impl_nil in H2. subst. reflexivity.
  Case "b2 = S b2".
    destruct l1.
      SCase "l1 = []".
        destruct l2; simpl in H; rewrite <- H; rewrite <- minus_n_O; simpl; reflexivity.
      SCase "l1 = a :: l1".
        destruct l2.
        SSCase "l2 = []".
          simpl in H1. assert (S b2 = 0) by omega. assert (b1 = 0) by omega.
          rewrite H2. rewrite H3. simpl. subst. apply length_0_impl_nil in H3.
          inversion H3.
        SSCase "l2 = p0 :: l2".
          destruct b1.
          SSSCase "b1 = 0".
            simpl. inversion H.
          SSSCase "b1 = S b1".
            replace (S b2 - S b1) with (b2 - b1) by omega.
            rewrite <- app_comm_cons. simpl. simpl in H. apply IHb2; omega.
Qed.


Theorem cut_right_preserves_all_keys: forall (X: Type) (b: nat) (P: nat -> Prop) (l: list (nat * X)),
  all_keys X P l -> all_keys X P (cut_list_right b l).
Proof.
  intros. generalize dependent b.
  induction l.
  Case "l = []".
    intros.
    destruct b.
    SCase "b = 0". 
      simpl. apply ak_empty.
    SCase "b = S b".
      simpl. apply ak_empty.
  Case "l = a::l".
    intros.
    destruct b.
    SCase "b = 0".
      simpl. apply H.
    SCase "b = S b".
      simpl. apply IHl. inversion H. apply H2.
Qed. 





    