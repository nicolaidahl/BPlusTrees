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

Theorem insert_into_list_works : forall (X: Type) (l: list (nat * X)) (k: nat) (v: X),
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
    



(* Some props for having a prop apply to all elements in a list *)
Inductive all_values (X : Type) (P : X -> Prop) : list (nat * X) -> Prop :=
  | av_empty : all_values X P []
  | av_next : forall (x:X) (n: nat) (l: list (nat * X)), all_values X P l -> P x -> all_values X P ((n,x)::l)
.
Inductive all_keys (X : Type) (P : nat -> Prop) : list (nat * X) -> Prop :=
  | ak_empty : all_keys X P []
  | ak_next : forall (x:X) (n: nat) (l: list (nat * X)), all_keys X P l -> P n -> all_keys X P ((n,x)::l)
.

(* Some helper functions for checking if a number is above or below a given number *)
Definition below (n: nat) : nat -> Prop :=
  fun o => blt_nat o n = true. 
Definition between (n m: nat) : nat -> Prop :=
  fun o => andb (ble_nat n o) (blt_nat o m) = true.
Definition above (m: nat) : nat -> Prop :=
  fun o => ble_nat m o = true.

(* Prop for determining if the splitting points indicated actually are splits *)
Inductive valid_splits' (b: nat) (X: Type) : list (nat * bplustree b X) -> Prop :=
  | valid_p : forall (t1 t2: bplustree b X) (n1 n2: nat) (l: list (nat * bplustree b X)),
              all_keys X (between n1 n2) (all_members t1) ->
              valid_splits' b X ((n2, t2)::l) ->
              valid_splits' b X ((n1, t1)::(n2, t2)::l)
  | valid_ep : forall (t: bplustree b X) (n: nat),
               all_keys X (above n) (all_members t) ->
               valid_splits' b X ((n, t)::[]).
Inductive valid_splits (b: nat) (X: Type) : bplustree b X -> list (nat * bplustree b X) -> Prop :=
  | valid_sp : forall (t1 t2: bplustree b X) (n: nat) (l: list (nat * bplustree b X)),
               all_keys X (below n) (all_members t1) ->
               valid_splits' b X ((n, t2)::l) -> 
               valid_splits b X t1 ((n, t2)::l).

(* Prop for determining if a subtree is a valid subtree *)
Inductive valid_sub_bplustree (b: nat) (X: Type) : bplustree b X -> Prop :=
  | valid_leaf : forall (l: list (nat * X)), 
                     b <> 0 ->
                     b <= length(l) -> 
                     length(l) <= mult b 2 ->
                     kvl_sorted l ->  
                     valid_sub_bplustree b X (bptLeaf b X l)
  | valid_node : forall (sp: bplustree b X) (kpl: list (nat * bplustree b X)),
                      b <> 0 -> 
                      b <= length(kpl) -> 
                      length(kpl) <= mult b 2 -> 
                      valid_sub_bplustree b X sp ->
                      all_values (bplustree b X) (valid_sub_bplustree b X) kpl ->
                      kvl_sorted kpl ->
                      valid_splits b X sp kpl -> 
                      valid_sub_bplustree b X (bptNode b X sp kpl)   
.

(* Main prop that determines if an entire B+-tree is valid *)
Inductive valid_bplustree (b: nat) (X: Type) : bplustree b X -> Prop :=
  | root_is_a_leaf : forall (l: list (nat * X)), 
                     b <> 0 ->
                     length(l) <= mult b 2 ->
                     kvl_sorted l ->  
                     valid_bplustree b X (bptLeaf b X l)
  | valid_root_node : forall (sp: bplustree b X) (kpl: list (nat * bplustree b X)),
                      b <> 0 -> 
                      length(kpl) <> 0 -> 
                      length(kpl) <= mult b 2 -> 
                      valid_sub_bplustree b X sp ->
                      all_values (bplustree b X) (valid_sub_bplustree b X) kpl ->
                      kvl_sorted kpl -> 
                      valid_splits b X sp kpl -> 
                      valid_bplustree b X (bptNode b X sp kpl)   
.

(* Some smaller examples *)
Example valid_empty_tree : valid_bplustree 1 nat (bptLeaf 1 nat []).
Proof. apply root_is_a_leaf. omega. simpl. omega. apply kvl_sorted_0. Qed.
Example valid_tiny_tree : valid_bplustree 1 nat (bptLeaf 1 nat [(1, 11), (2,22)]).
Proof.  apply root_is_a_leaf. omega. simpl. omega. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. Qed.
Example invalid_bigger_tree : ~ (valid_bplustree 1 nat (bptLeaf 1 nat [(1, 11), (2,22), (3, 33)])).
Proof. unfold not. intro. inversion H. simpl in H2. inversion H2. inversion H5. inversion H7. Qed.

(* 3 Examples all showing the same - that our demo `root` B+-tree is valid *)
Example valid_small_tree : valid_bplustree 1 nat root.
Proof. compute. apply valid_root_node. 
  Case "valid b". omega.
  Case "has enough items". simpl. omega.
  Case "doesnt have too many items". simpl. omega. 
  Case "sp". apply valid_leaf. omega. simpl.  omega. simpl. omega. apply kvl_sorted_1.
  Case "kvl". apply av_next. apply av_next. apply av_empty.
    apply valid_leaf. omega. simpl. omega.  simpl. omega. apply kvl_sorted_1.
    apply valid_leaf. omega. simpl. omega.  simpl. omega. apply kvl_sorted_1.
  Case "valid sorting". 
    apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity.
  Case "valid splits". 
  apply valid_sp. apply ak_next. apply ak_empty. reflexivity.
  apply valid_p. apply ak_next. apply ak_empty. reflexivity.
  apply valid_ep. apply ak_next. apply ak_empty. reflexivity.
Qed.
Example valid_small_tree' : valid_bplustree 1 nat root.
Proof. compute.
  constructor. 
  Case "valid b". omega.
  Case "has enough items". simpl. omega.
  Case "doesnt have too many items". simpl. omega. 
  Case "sp". repeat constructor. omega. 
  Case "kvl". repeat constructor. omega. omega.
  Case "valid sorting". repeat constructor.
  Case "valid splits". repeat constructor.
Qed.
Example valid_small_tree'' : valid_bplustree 1 nat root.
Proof. compute. repeat constructor; simpl; omega. Qed.

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

    