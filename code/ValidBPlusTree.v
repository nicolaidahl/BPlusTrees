Require Import InductiveDataTypes.
Require Import BPlusTree.


Definition equal_height {X: Type} {b: nat}: bplustree b X -> bplustree b X -> Prop :=
  fun n m => beq_nat (height n) (height m) = true.


(* Prop for determining if the splitting points indicated actually are splits *)
Inductive valid_splits (b: nat) (X: Type) : list (nat * bplustree b X) -> Prop :=
  | valid_p : forall (t1 t2: bplustree b X) (n1 n2: nat) (l: list (nat * bplustree b X)),
              all_keys X (between n1 n2) (inorder t1) ->
              valid_splits b X ((n2, t2)::l) ->
              valid_splits b X ((n1, t1)::(n2, t2)::l)
  | valid_ep : forall (t: bplustree b X) (n: nat),
               all_keys X (above n) (inorder t) ->
               valid_splits b X ((n, t)::[]).

(* Prop for determining if a subtree is a valid subtree *)
Inductive valid_sub_bplustree (b: nat) (X: Type) : bplustree b X -> Prop :=
  | valid_leaf : forall (l: list (nat * X)), 
                     b <> 0 ->
                     b <= length(l) -> 
                     length(l) <= mult b 2 ->
                     kvl_sorted l ->  
                     valid_sub_bplustree b X (bptLeaf b X l)
  | valid_node : forall (kpl: list (nat * bplustree b X)),
                      b <> 0 -> 
                      S b <= length(kpl) -> 
                      length(kpl) <= S (mult b 2) ->
                      key_at_index 0 kpl = Some 0 -> 
                      all_values (bplustree b X) (valid_sub_bplustree b X) kpl ->
                      all_values_eq_prop (bplustree b X) equal_height kpl ->
                      kvl_sorted kpl ->
                      valid_splits b X kpl -> 
                      valid_sub_bplustree b X (bptNode b X kpl)   
.

(* Main prop that determines if an entire B+-tree is valid *)
Inductive valid_bplustree (b: nat) (X: Type) : bplustree b X -> Prop :=
  | root_is_a_leaf  : forall (kvl: list (nat * X)), 
                      b <> 0 ->
                      length kvl <= b * 2 ->
                      kvl_sorted kvl ->  
                      valid_bplustree b X (bptLeaf b X kvl)
  | valid_root_node : forall (kpl: list (nat * bplustree b X)),
                      b <> 0 -> 
                      2 <= length kpl -> 
                      length kpl <= S (b * 2) ->
                      key_at_index 0 kpl = Some 0 -> 
                      all_values (bplustree b X) (valid_sub_bplustree b X) kpl ->
                      all_values_eq_prop (bplustree b X) equal_height kpl ->
                      kvl_sorted kpl ->  
                      valid_splits b X kpl ->
                      valid_bplustree b X (bptNode b X kpl)   
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
  Case "first key is 0". simpl. reflexivity.
  Case "kvl". apply av_next. apply av_next. apply av_next. apply av_empty.
    apply valid_leaf. omega. simpl. omega.  simpl. omega. apply kvl_sorted_1.
    apply valid_leaf. omega. simpl. omega.  simpl. omega. apply kvl_sorted_1.
    apply valid_leaf. omega. simpl. omega.  simpl. omega. apply kvl_sorted_1.
  Case "valid height".
    repeat apply alep_next; unfold equal_height; simpl; try reflexivity. apply alep_1. 
  Case "valid sorting". 
    apply kvl_sorted_cons. apply kvl_sorted_cons. apply kvl_sorted_1. reflexivity. reflexivity.
  Case "valid splits". 
  apply valid_p. apply ak_next. apply ak_empty. reflexivity.
  apply valid_p. apply ak_next. apply ak_empty. reflexivity.
  apply valid_ep. apply ak_next. apply ak_empty. reflexivity.
Qed.
Example valid_small_tree' : valid_bplustree 1 nat root.
Proof. compute.
  constructor. 
  Case "valid b". omega.
  Case "has enough items". simpl. omega.
  Case "doesnt have too many items". simpl. omega.
  Case "first key is 0". reflexivity.  
  Case "kvl". repeat constructor. omega. omega. omega.
  Case "valid height". repeat constructor.
  Case "valid sorting". repeat constructor.
  Case "valid splits". repeat constructor.
Qed.
Example valid_small_tree'' : valid_bplustree 1 nat root.
Proof. compute. repeat constructor; simpl; omega. Qed.


Lemma valid_sub_bplustree_impl_valid_bplustree : forall {X: Type} {b: nat} (tree: bplustree b X),
  valid_sub_bplustree b X tree -> valid_bplustree b X tree.
Proof.
  intros.
  inversion H; constructor; try assumption.
  omega.
Qed.
