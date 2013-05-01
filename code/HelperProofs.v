Require Export SfLib.
Require Export HelperFunctions.
Require Export BPlusTree.

(* 
 * Proofs about blt_nat
 *)
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

Lemma n_lt_n_inversion : forall (n: nat) (P: Prop),
  n < n -> P.
Proof.
  intros. apply lt_not_le in H. unfold not in H. 
  apply ex_falso_quodlibet. apply H.
  omega.
Qed.

Lemma Sn_le_n_inversion : forall (n: nat) (P: Prop),
  S n <= n -> P.
Proof.
  intros. apply le_not_gt in H. unfold not in H.
  apply ex_falso_quodlibet. apply H.
  omega.
Qed.


Lemma ble_nat_symm : forall (n: nat),
  ble_nat n n = true.
Proof.
  intros. induction n.
  simpl. reflexivity.
  simpl. apply IHn.
Qed.

Lemma blt_nat_symm : forall (n: nat),
  blt_nat n n = false.
Proof.
  intros. induction n.
  unfold blt_nat. simpl. reflexivity.
  apply blt_nat_n_m_false__blt_nat_Sn_Sm. apply IHn.
Qed.

(*
 * Proofs about min_nat
 *)
Theorem min_nat_works : forall (n1 n2: nat),
  (n2 < n1 -> min_nat n2 n1 = n2) /\ (n1 > n2 -> min_nat n2 n1 = n2).
Proof.
  intros n1 n2;
  split; intros;
    unfold min_nat; remember (ble_nat n2 n1) as ble; destruct ble;
    try reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
 Qed.
  
Theorem min_nat_elim_n1 : forall (n1 n2: nat),
  n1 <= n2 <-> min_nat n1 n2 = n1.
Proof.
  split.
  Case "->".
    intros. unfold min_nat. remember (ble_nat n1 n2) as ble. destruct ble.
    reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold min_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.

Theorem min_nat_elim_n2 : forall (n1 n2: nat),
  n1 >= n2 <-> min_nat n1 n2 = n2.
Proof.
  split.
  Case "->".
    intros. unfold min_nat. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold min_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.



(*
 * Proofs about max_nat
 *)
Theorem max_nat_works : forall (n1 n2: nat),
  (n1 < n2 -> max_nat n1 n2 = n2) /\ (n2 < n1 -> max_nat n1 n2 = n1). 
Proof.
  intros n1 n2.
  split; intros; 
    unfold max_nat; remember (ble_nat n1 n2) as ble; destruct ble; 
    try reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
Qed.

Theorem max_nat_elim_n1 : forall (n1 n2: nat),
  n1 <= n2 <-> max_nat n1 n2 = n2.
Proof.
  split.
  Case "->".
    intros. unfold max_nat. remember (ble_nat n1 n2) as ble. destruct ble.
    reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold max_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.
    
Theorem max_nat_elim_n2 : forall (n1 n2: nat),
  n1 >= n2 <-> max_nat n1 n2 = n1.
Proof.
  split.
  Case "->".
    intros. unfold max_nat. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
  Case "<-".
    intros. unfold max_nat in H. remember (ble_nat n1 n2) as ble. destruct ble;
    symmetry in Heqble. apply ble_nat_true in Heqble. omega.
    apply ble_nat_false in Heqble. omega.
Qed.

Lemma eq_remove_S : forall (n m: nat),
  n = m -> S n = S m.
Proof.
  intros.
  omega.
Qed.

(*
 * Lenght lemmas
 *)
Lemma length_0_impl_nil : forall (X: Type) (l: list X),
  length l = 0 -> l = [].
Proof.
  intros. induction l.
  reflexivity.
  simpl in H. inversion H.
Qed.
Lemma length_gt_0_impl_nil : forall (X: Type) (l: list X),
  length l <= 0 -> l = [].
Proof.
  intros. induction l.
  reflexivity.
  simpl in H. inversion H.
Qed.


Lemma app_length_le_l1 : forall (X: Type) (l l1 l2: list X),
  l1 ++ l2 = l -> length l1 <= length l.
Proof.
  intros. generalize dependent l1.
  induction l.
  Case "l = []".
    intros. apply app_eq_nil in H. inversion H. subst. simpl. omega.
  Case "l = a::l".
    intros. destruct l1. simpl. omega.
    rewrite <- app_comm_cons in H.
    inversion H. rewrite H2.
    simpl. apply le_n_S. apply IHl. apply H2.
Qed.

Lemma rev_app_cons : forall (X: Type) (x: X) (l1 l2: list X),
  rev l1 ++ x :: l2 = rev (x::l1) ++ l2.
Proof.
  intros. simpl. rewrite <- app_assoc. simpl. reflexivity.
Qed.

    
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

Lemma app_list_eq_list_list : forall (X: Type) (l1 l2: list X),
  l1 ++ l2 = l1 -> l2 = [].
Proof.
  intros.
  induction l1. simpl in H. apply H.
  apply IHl1. simpl in H. SearchAbout [cons].
  inversion H. rewrite H1. apply H1.
Qed.

Theorem split_list'_preserves_lists : forall (X: Type) (b: nat) (l l1 l2 l3: list X),
   split_list' b l3 l = ((rev l3)++l1, l2) -> l = l1 ++ l2 /\ length l1 = b.
Proof.
  intros. generalize dependent l3.
  induction b.
  Case "b = 0".
    intros. simpl in H.
    inversion H. 
    symmetry in H1. apply app_list_eq_list_list in H1.
    subst.
    simpl.
    split; reflexivity.
  Case "b = S b".
    admit.
Admitted.

Theorem split_list_preserves_lists : forall (X: Type) (b: nat) (l l1 l2: list X),
   split_list b l = (l1, l2) -> l = l1 ++ l2 /\ length l1 = b.
Proof.
  intros.
  unfold split_list in H. replace (l1) with ((rev [])++l1) in H by reflexivity.
  apply split_list'_preserves_lists in H. apply H.
Qed.

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
    apply H2.
  Case "b = S b".
    intros.
    apply split_list_preserves_lists in H1. inversion H1.
    destruct l1; simpl in H3; inversion H3.
    rewrite <- app_comm_cons. rewrite <- app_comm_cons in *.
    destruct l; inversion H2.
    reflexivity.
Qed.

Lemma element_at_index_sorted : forall (X: Type) (b k1: nat) (v1: X) (l l1 l2: list (nat * X)),
  b <> 0 -> b = length l1 -> kvl_sorted l -> element_at_index b l = Some (k1, v1) -> 
  split_list b l = (l1, (k1,v1)::l2) ->
  l = l1 ++ (k1, v1)::l2 /\ kvl_sorted (l1) /\ kvl_sorted ((k1, v1)::l2). 
Proof.
  admit.
Admitted.

Lemma list_eq_impl_length_eq : forall (X: Type) (l1 l2: list X),
  l1 = l2 -> length l1 = length l2.
Proof.
  intros.
  subst. reflexivity.
Qed.

Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall skb v l, appears_in_kvl sk l -> appears_in_kvl sk ((skb, v)::l).

Lemma element_at_index_impl_appears: forall (X: Type) (b k: nat) (v: X) (l: list (nat*X)),
  element_at_index b l = Some (k, v) -> appears_in_kvl k l.
Proof.
  admit.
Admitted.

Lemma appears_in_kvl_app : forall (X: Type) (k: nat) (l: list (nat*X)),
  appears_in_kvl k l -> exists l1, exists l2, exists v, l = l1++(k,v)::l2.
Proof.
  admit.
Admitted.

