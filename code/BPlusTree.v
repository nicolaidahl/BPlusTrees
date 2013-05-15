Require Export SfLib.
Require Export HelperFunctions.
Require Export SplitCutList.
Require Export InductiveDataTypes.

(* Helper functions to retrieve the leftmost key *)
Fixpoint leftmost_key {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  match tree with
  | bptLeaf (x :: _) => fst x
  | bptNode (_ :: x :: _) => fst x
  | _ => 0
  end.
  
Fixpoint leftmost_key_deep {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  match tree with
  | bptLeaf (x :: _) => fst x
  | bptNode (x :: _) => leftmost_key_deep (snd x)
  | _ => 0
  end.

Definition left := bptLeaf 1 nat [(5, 55)].
Definition centre := bptLeaf 1 nat [(7, 77)].
Definition right := bptLeaf 1 nat [(9, 99)].
Definition root := bptNode 1 nat [(0, left), (leftmost_key centre, centre), (leftmost_key right, right)].

(* Height *)
Fixpoint height {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  match tree with
    | bptLeaf _ => 0
    | bptNode [] => 0
    | bptNode ((_, subtree)::_) => S (height (subtree))
  end.

Example height_1 : height root = 1.
Proof. simpl. reflexivity. Qed.
Example height_2 : height (bptNode 1 nat [(1, bptNode 1 nat [(0, bptLeaf 1 nat [(2, 102)])])]) = 2.
Proof. simpl. reflexivity. Qed.
Example height_3 : height 
(bptNode 1 nat [(1, bptNode 1 nat 
               [(0, bptNode 1 nat 
               [(3, bptNode 1 nat 
               [(1, bptLeaf 1 nat [(2, 102)])])])])]) = 4.
Proof. simpl. reflexivity. Qed. 

(* Search *)
Fixpoint search_leaf {X: Type} (sk: nat) (kvl: (list (nat * X))) : option X :=
  match kvl with
    | nil => None
    | (k, v) :: kvl' => if beq_nat k sk then Some v else search_leaf sk kvl'
  end.

Fixpoint find_subtree {X: Type} {b: nat} (sk: nat) (kpl: list (nat * bplustree b X)) : option (nat * bplustree b X) :=
  match kpl with
    | [] => None
    | (k, last_tree) :: [] => if ble_nat k sk then Some (k, last_tree) else None
    | (k1, subtree) :: ((k2, _) :: _) as kpl' => if ble_nat k1 sk && blt_nat sk k2
                                                   then Some (k1, subtree)
                                                   else find_subtree sk kpl'
  end.

Fixpoint search' {X: Type} {b: nat} (counter sk: nat) (tree: bplustree b X) {struct counter}: option X :=
  match (counter, tree) with
    | (_, bptLeaf kvl) => search_leaf sk kvl
    | (0, _) => None
    | (S counter', bptNode kpl) => match find_subtree sk kpl with
      | Some (_, subtree) => search' counter' sk subtree
      | None => None
    end
  end.

Definition search {X: Type} {b: nat} (sk: nat) (tree: bplustree b X) : option X :=
  search' (height tree) sk tree.

Example search_test_find_item_left : search 4 root = None.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_centre : search 7 root = Some 77.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 9 root = Some 99.
Proof. unfold root. unfold leftmost_key. simpl. reflexivity. Qed.
Example search_test_cant_find_missing : search 6 root = None.
Proof. simpl. reflexivity. Qed.

Fixpoint inorder {X: Type} {b: nat} (tree: (bplustree b X)) : list (nat * X) :=
  let fix node_members (kpl: (list (nat * bplustree b X))) : list (nat * X) :=
    match kpl with
      | nil => []
      | (k, p) :: kpl' => (inorder p) ++ (node_members kpl')
    end
  in
  match tree with
    | bptLeaf kpl => kpl
    | bptNode kpl => (node_members kpl)
  end.

Example all_members_left : inorder left = [(5, 55)].
Proof. simpl. reflexivity. Qed.
Example all_members_root : inorder root = [(5, 55), (7, 77), (9, 99)].
Proof. simpl. reflexivity. Qed.

(* Insertion *)
(* Leafs *)
Fixpoint insert_into_list {X: Type} (k: nat) (v: X) (kvl: list (nat * X)) : list (nat * X) :=
  match kvl with 
    | nil => [(k, v)]
    | (k', v') :: kvl' => if ble_nat k k'
    					  then 
    						if beq_nat k k' 
    						then ((k, v) :: kvl') 
    						else ((k, v) :: kvl)
    					  else (k', v') :: (insert_into_list k v kvl')
  end.



Definition insert_leaf {X: Type} (b: nat) (k: nat) (v: X) (kvl: list (nat * X))
						: (list (nat * X) * option (list (nat * X))) :=
  let kvl' := insert_into_list k v kvl
  in
    if ble_nat (length kvl') (b * 2)
      then (kvl', None)
      else let (fst, snd) := split_list b kvl' in (fst, Some snd) 
  .

(* Nodes *)
Definition split_if_necessary {X: Type} {b: nat} (tree: (bplustree b X))
  							: (bplustree b X * option (nat * bplustree b X)) := 
  match tree with
  	| bptLeaf kvl => (tree, None)
  	| bptNode kpl => 
  	  if ble_nat (length kpl) ((b * 2) + 1)
        then (tree, None)
        else match (split_list (b + 1) kpl) with
          | (fst, []) => (bptNode b X fst, None)
          | (fst, (lmk,lmt)::snd') =>  
            (bptNode b X fst, Some (lmk, bptNode b X ((0, lmt)::snd')))
        end
          (*  
            
          let (fst, snd) := split_list (b + 1) kpl in
          let new_node := bptNode b X snd in
          (bptNode b X fst, Some (leftmost_key_deep new_node, new_node))
          *)
  end. 

Definition insert_node {X: Type} {b: nat} (insertion_key: nat) (old_tree: (bplustree b X)) 
                       (input: (bplustree b X * option (nat * bplustree b X)))
  					   : (bplustree b X * option (nat * bplustree b X)) :=
  match old_tree with
  	| bptLeaf kvl => input
  	| bptNode kpl =>
  	  match input with
        | (t, None) => (bptNode b X (insert_into_list insertion_key t kpl), None)
              (* No overflow, just replace the pointer with key = insertion_key *)
  		| (t, Some (new_key, new_tree)) => split_if_necessary (
  		                                     bptNode b X (
  		                                       insert_into_list insertion_key t (
  		                                         insert_into_list new_key new_tree kpl)))
  		      (* Overflowed, so replace the tree with key = insertion_key, and 
  		       * add the overflow new_tree too. In case this node then overflows,
  		       * we split_if_necessary, that will split if it overflows *)
  	  end
  end.
  
Fixpoint insert' {X: Type} {b: nat} (counter k: nat) (v: X) (tree: (bplustree b X))
                : (bplustree b X * option (nat * bplustree b X)) :=
  match (tree, counter) with
    | (bptLeaf kvl, _) => let (fst, snd_opt) := insert_leaf b k v kvl in
                     match snd_opt with
                     | None => (bptLeaf b X fst, None)
                     | Some snd => 
                         match key_at_index 0 snd with
                         | None => (bptLeaf b X fst, None)
                         | Some first_key => (bptLeaf b X fst, Some (first_key, bptLeaf b X snd))
                         end
                     end
    | (_, 0) => (tree, None)
    | (bptNode kpl, S counter') => match find_subtree k kpl with
      | None => (tree, None)
      | Some (key, subtree) => insert_node key tree (insert' counter' k v subtree)
    end
  end. 


Definition insert {X: Type} {b: nat} (k: nat) (v: X) (tree: (bplustree b X))
                : bplustree b X :=
  match insert' (height tree) k v tree with
    | (tree, None) => tree
    | (left, Some (key, right)) => bptNode b X [(0, left), (key, right)]
  end.

Definition empty2Tree := bptLeaf 1 nat [].
Eval compute in insert 3 103 (insert 2 102 (insert 1 101 empty2Tree)).
Eval compute in insert 4 104 (insert 3 103 (insert 2 102 (insert 1 101 empty2Tree))).  
Eval compute in insert 5 105 (insert 4 104 (insert 3 103 (insert 2 102 (insert 1 101 empty2Tree)))).

(* List2Bplustree *)
Fixpoint list2bplustree' {b: nat} {X: Type} (l: list (nat * X)) (tree: bplustree b X) : bplustree b X :=
  match l with
    | []          => tree
    | (k, v) :: l' => list2bplustree' l' (insert k v tree)
  end.

Definition list2bplustree (b: nat) {X: Type} (l: list (nat * X)) : bplustree b X :=
  match l with
    | []          => bptLeaf b X []
    | (k, v) :: l => list2bplustree' l (bptLeaf b X [(k, v)])
  end.

Eval compute in (list2bplustree 1 [(4, 4), (2, 2), (3, 3), (1, 1)]).
Eval compute in (list2bplustree 1 [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]).
  
Example list2bplustree_empty : list2bplustree 2 [] = bptLeaf 2 nat [].
Proof. simpl. reflexivity. Qed.
Example list2bplustree_1 : list2bplustree 4 [(1, 1)] = bptLeaf 4 nat [(1, 1)].
Proof. simpl. reflexivity. Qed.
Example list2bplustree_4 : list2bplustree 1 [(4, 4), (2, 2), (3, 3), (1, 1)] = bptNode 1 nat
         [(0, [[1,nat|(1, 1),(2, 2)]]), (3, [[1,nat|(3, 3),
                                                  (4, 4)]])].
Proof. compute. reflexivity. Qed.

Example list2bplustree_6 : (list2bplustree 1 [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]) = 
bptNode 1 nat
         [(0, bptNode 1 nat [(0, [[1,nat|(1, 1)]]), (2, [[1,nat|(2, 2)]])]),
         (3,
         bptNode 1 nat
           [(0, [[1,nat|(3, 3)]]), (4, [[1,nat|(4, 4)]]),
           (5, [[1,nat|(5, 5),(6, 6)]])])].
Proof. compute. reflexivity. Qed.

Definition bigtree := list2bplustree 1 [(11, 1), (22, 2), (33, 3), (44, 4), (55, 5), (66, 6), (77, 7)].

Eval compute in (bigtree).
Eval compute in (height bigtree).


