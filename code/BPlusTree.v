Require Export SfLib.
Require Export HelperFunctions.
Require Export SplitCutList.
Require Export InductiveDataTypes.

  


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

Fixpoint search_leaf {X: Type} (sk: nat) (kvl: (list (nat * X))) : option X :=
  match kvl with
    | nil => None
    | (k, v) :: kvl' => if beq_nat k sk then Some v else search_leaf sk kvl'
  end.

Fixpoint search {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X)) : option X :=  
  
  let fix search_node (kpl: (list (nat * bplustree b X))): option X :=
      match kpl with
        | nil => None
        | (_, t1) :: kpl' => match kpl' with
                             | nil => search sk t1
                             | (k2, t2) :: _ =>
							   if blt_nat sk k2
							   then search sk t1
							   else search_node kpl'
							 end
      end 
  in
    
  match tree with
  | bptLeaf kvl => search_leaf sk kvl
  | bptNode kpl' => search_node kpl'
  end.
  
  

Example search_test_find_item_left : search 4 root = None.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_centre : search 7 root = Some 77.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 9 root = Some 99.
Proof. unfold root. unfold leftmost_key. simpl. reflexivity. Qed.
Example search_test_cant_find_missing : search 6 root = None.
Proof. simpl. reflexivity. Qed.

Fixpoint all_members {X: Type} {b: nat} (tree: (bplustree b X)) : list (nat * X) :=
  let fix node_members (kpl: (list (nat * bplustree b X))) : list (nat * X) :=
    match kpl with
      | nil => []
      | (k, p) :: kpl' => (all_members p) ++ (node_members kpl')
    end
  in
  match tree with
    | bptLeaf kpl => kpl
    | bptNode kpl => (node_members kpl)
  end.

Example all_members_left : all_members left = [(5, 55)].
Proof. simpl. reflexivity. Qed.
Example all_members_root : all_members root = [(5, 55), (7, 77), (9, 99)].
Proof. simpl. reflexivity. Qed.

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

Definition split_if_necessary {X: Type} {b: nat} (tree: (bplustree b X))
  							: (bplustree b X * option (nat * bplustree b X)) := 
  match tree with
  	| bptLeaf kvl => (tree, None)
  	| bptNode kpl => 
  	  if ble_nat (length kpl) ((b * 2) + 1)
        then (tree, None)
        else 
          let (fst, snd) := split_list (b + 1) kpl in
          let new_node := bptNode b X snd in
          (bptNode b X fst, Some (leftmost_key_deep new_node, new_node))
  end. 

Definition insert_node {X: Type} {b: nat} (insertion_key: nat) (old_tree: (bplustree b X)) 
                       (input: (bplustree b X * option (nat * bplustree b X)))
  					   : (bplustree b X * option (nat * bplustree b X)) :=
  match old_tree with
  	| bptLeaf kvl => input
  	| bptNode kpl =>
      (* Replace the pointer with key = insertion_index *)
  	  match input with
        | (t, None) => (bptNode b X (insert_into_list insertion_key t kpl), None)
  		| (t, Some (new_key, new_tree)) => 
  		  split_if_necessary (bptNode b X (insert_into_list insertion_key t (insert_into_list new_key new_tree kpl)))
  	  end
  end.
  
Fixpoint insert' {X: Type} {b: nat} (k: nat) (v: X) (tree: (bplustree b X))
                : (bplustree b X * option (nat * bplustree b X)) :=

  (* More or less copy-pasted from search *)
  let fix insert_into_node (kpl: (list (nat * bplustree b X)))
                           : (bplustree b X * option (nat * bplustree b X)) :=
    match kpl with
      | nil => (tree, None)
      | (k1, p1) :: kpl' => match kpl' with
                           | nil => insert_node k1 tree (insert' k v p1) 
                           | (k2, p2) :: _ => if blt_nat k k2
                                              then insert_node k1 tree (insert' k v p1)
                                              else insert_into_node kpl' 
                           end
      
    end 
     
  in 
  
  match tree with
    | bptLeaf kvl => let (fst, snd_opt) := insert_leaf b k v kvl in
                     match snd_opt with
                     | None => (bptLeaf b X fst, None)
                     | Some snd => 
                         match key_at_index 0 snd with
                         | None => (bptLeaf b X fst, None)
                         | Some first_key => (bptLeaf b X fst, Some (first_key, bptLeaf b X snd))
                         end
                     end 
    | bptNode kpl => insert_into_node kpl
  end.

Definition insert {X: Type} {b: nat} (k: nat) (v: X) (tree: (bplustree b X))
                : bplustree b X :=
  match insert' k v tree with
    | (tree, None) => tree
    | (left, Some (key, right)) => bptNode b X [(0, left), (key, right)]
  end.

Definition empty2Tree := bptLeaf 1 nat [].

Eval compute in (root).
Eval compute in insert 3 103 (insert 2 102 (insert 1 101 empty2Tree)).
Eval compute in insert 4 104 (insert 3 103 (insert 2 102 (insert 1 101 empty2Tree))).  
Eval compute in insert 5 105 (insert 4 104 (insert 3 103 (insert 2 102 (insert 1 101 empty2Tree)))).


(* Height *)
Fixpoint height' {X: Type} {b: nat} (h: nat) (tree: bplustree b X) : nat :=
  let fix highest_in_list (h: nat) (tlist: list (nat * (bplustree b X))) : nat :=
	  match tlist with
	    | [] => h
	    | (k, tree) :: kvl => let new_h := (height' 0 tree) in
	                          if ble_nat new_h h
	                          then highest_in_list h kvl
	                          else highest_in_list new_h kvl
	  end
  in
  match tree with
    | bptLeaf kvl => h
    | bptNode kvl => (S h) + (highest_in_list 0 kvl)
  end.

Definition height {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  height' 0 tree.
  
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




(* Mindepth *)
Fixpoint mindepth' {X: Type} {b: nat} (h: nat) (tree: bplustree b X) : nat :=
  let fix lowest_in_list (h: nat) (tlist: list (nat * (bplustree b X))) : nat :=
    match tlist with
      | [] => h
      | (k, tree) :: kvl => let new_h := (mindepth' 0 tree) in 
                            if ble_nat new_h h
                            then lowest_in_list new_h kvl
                            else lowest_in_list h kvl
    end
  in
  match tree with
    | bptLeaf kvl => h
    | bptNode kvl => ((S h) + (lowest_in_list 0 kvl))
  end.
  
Definition mindepth {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  mindepth' 0 tree.

Definition mindepth_tree := (bptNode 1 nat [(22, bptNode 1 nat [(1, bptNode 1 nat [])])]).
Eval compute in (mindepth mindepth_tree).
Eval compute in (height mindepth_tree).

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
           [(3, [[1,nat|(3, 3)]]), (4, [[1,nat|(4, 4)]]),
           (5, [[1,nat|(5, 5),(6, 6)]])])].
Proof. compute. reflexivity. Qed.

Definition bigtree := list2bplustree 1 [(11, 1), (22, 2), (33, 3), (44, 4), (55, 5), (66, 6), (77, 7)].

Eval compute in (bigtree).
Eval compute in (height bigtree).
Eval compute in (mindepth' 0 bigtree). (*TODO fix*)


(*
(* Deletion *)
Fixpoint delete_from_list {X: Type} (sk: nat) (lst: list (nat * X))
                          : list (nat * X) :=
  match lst with
  | nil => nil
  | (k, v) :: xs => if beq_nat k sk 
                    then xs 
                    else (k,v) :: delete_from_list sk xs
                         
  end.

Definition node_length {X: Type} {b: nat} (tree: bplustree b X): nat :=
  match tree with
  | bptLeaf kvl => length kvl
  | bptNode sp nodes => length nodes
  end.
  
Eval simpl in node_length root.

Definition merge_trees {X: Type} {b:nat} (t1 t2: bplustree b X)
                       : bplustree b X :=
  match (t1, t2) with
  | (bptNode sp1 lst1, bptNode sp2 lst2) => 
      bptNode b X sp1 (app lst1 ((peek_key_deep sp2, sp2) :: lst2))
  | (bptLeaf lst1, bptLeaf lst2) => bptLeaf b X (app lst1 lst2)
  | _ => t1
  end. 

Definition distr_betweentwo {X: Type} {b: nat} (t1 t2: bplustree b X)
                             : (bplustree b X * bplustree b X) :=
  match (t1, t2) with
  | (bptNode sp1 lst1, bptNode sp2 lst2) => 
    if blt_nat (length lst1) b (*the list of t1 is too small*)
    then 
      (* Here I plus by 1 as the sp2 is being added to lst1 no matter what *)
      let index_to_split_list2 := minus b (S (length lst1)) in 
      let (part1, part2) := split_at_index lst2 index_to_split_list2 in
      
      let ret_tree1 := bptNode b X sp1 ((snoc lst1 (peek_key_deep sp2, sp2)) ++ part1) in
      
      let new_list2_sp := match head part2 with
                          | None => sp2
                          | Some p => snd p
                          end in
      let new_list2 := match tail part2 with
                       | None => nil
                       | Some xs => xs
                       end in
                       
      let ret_tree2 := bptNode b X new_list2_sp new_list2 in
      (ret_tree1, ret_tree2)
       
    else (* the list of t2 is too small*)
      let index_to_split_list1 := minus (length lst1) (minus b (length lst2)) in
      let (part1, part2) := split_at_index lst1 index_to_split_list1 in
      
      let ret_tree1 := bptNode b X sp1 part1 in
      
      let new_list2_sp := match head part2 with
                          | None => sp2
                          | Some p => snd p
                          end in
      let tail_of_part2 := match tail part2 with
                       | None => nil
                       | Some xs => xs
                       end in
                       
      let ret_tree2 := bptNode b X new_list2_sp (app (tail_of_part2) ((peek_key_deep sp2, sp2) :: lst2)) in
      
      (ret_tree1, ret_tree2)
  | (bptLeaf kvl1, bptLeaf kvl2) => 
    let (first_half, second_half) := split_in_half (app kvl1 kvl2) in
    (bptLeaf b X first_half, bptLeaf b X second_half) 
  | _ => (t1, t2) 
  end.
  
Definition leaf := bptLeaf 1 nat [(1, 1)].
Definition emptyNode := bptNode 1 nat left [].
Definition twoEntriesNode := bptNode 1 nat leaf [(peek_key centre, centre), (peek_key right, right)].

Eval compute in twoEntriesNode.
Eval compute in emptyNode.
Eval compute in distr_betweentwo twoEntriesNode emptyNode.


Fixpoint redistribute_list {X: Type} {b: nat} (nodes: list (nat * bplustree b X))
                     : (list (nat * bplustree b X) * bool) :=
  match nodes with
  | nil => (nil, false)
  | x1 :: xs1 => 
         match xs1 with
	     | nil => ([x1], false)
	     | x2 :: nil => if blt_nat (node_length (snd x1)) b
	                    then
	             		  if beq_nat (node_length (snd x2)) b
	             		  then 
	               			let merge_res := merge_trees (snd x1) (snd x2) in
	               			([(peek_key_deep merge_res, merge_res)], true)
	             		  else 
	               			let (a, b) := distr_betweentwo (snd x1) (snd x2) in
	               			((peek_key_deep a, a) :: (peek_key_deep b, b) :: nil, false)
	           			else if blt_nat (node_length (snd x2)) b
	                	then
	                  	  if beq_nat (node_length (snd x1)) b
	                  	  then 
	                    	let merge_res := merge_trees (snd x1) (snd x2) in
	                    	([(peek_key_deep merge_res, merge_res)], true)
	                  	  else 
	                    	let (a, b) := distr_betweentwo (snd x1) (snd x2) in
	                    	((peek_key_deep a, a) :: (peek_key_deep b, b) :: nil, false)
	                	else
	                  	  (x1 :: x2 :: nil, false)
	     | x2 :: xs2 => if blt_nat (node_length (snd x1)) b
	                    then 
	                      if beq_nat (node_length (snd x2)) b
	                      then 
	                        let merge_res := merge_trees (snd x1) (snd x2) in
	                        ((peek_key_deep merge_res, merge_res) :: xs2, true)
	                      else 
	                        let (a, b) := distr_betweentwo (snd x1) (snd x2) in
	                        ((peek_key_deep a, a) :: (peek_key_deep b, b) :: xs2, false)
	                    else
	                      let (res, should_balance) := redistribute_list xs1 in
	                      (x1 :: res, should_balance)
	     end
  end.

Definition redistribute {X: Type} {b: nat} (tree: bplustree b X)
                            : (bplustree b X * bool) :=
  match tree with
  | bptLeaf kvl => (tree, false)
  | bptNode sp nil => (tree, true)
  | bptNode sp lst => 
    let (res, should_balance) := redistribute_list ((peek_key_deep sp, sp) :: lst) in
    match res with
    | nil => (bptNode b X sp res, should_balance) (*Should never be a possibility*)
    | (k, v) :: xs => (bptNode b X v xs, should_balance) 
    end
  end.

Definition balance {X: Type} {b: nat} (tree_ind: bplustree b X * bool)
                            : bplustree b X * bool :=
  match snd tree_ind with
  | false => (fst tree_ind, false)
  | true  => redistribute (fst tree_ind)
  end.
  
  
(* Returns a tree that it has deleted an entry from, a bool indicating if balancing should
   be performed *)
Fixpoint delete' {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X))
                : (bplustree b X * bool) :=
  
  let fix traverse_node (nptrs: list (nat * (bplustree b X)))
                   : (list (nat * (bplustree b X)) * bool) :=
    match nptrs with
    | nil => (nil, false)
    | (k1,t1) :: xs => match xs with
                       | nil => let (new_tree, should_balance) := delete' sk t1 in
                                  (((peek_key_deep new_tree, new_tree) :: xs), should_balance) 
                       
                       | (k2, t2) :: xs' => if blt_nat sk k2 
                                            then 
                                              let (new_tree, should_balance) := delete' sk t1 in
                                			    (((peek_key_deep new_tree, new_tree) :: xs), should_balance)
                                			  
                                            else 
                                              let (traversed, should_balance) := traverse_node xs in
                       						  ((k1,t1) :: traversed, should_balance)			  
                       end
    end
  
  in
  
  match tree with
  | bptLeaf kvl => let deletion_lst := delete_from_list sk kvl in 
                     if blt_nat (length deletion_lst) b 
                     then (bptLeaf b X deletion_lst, true)
                     else (bptLeaf b X deletion_lst, false)
  | bptNode sp nil => 
                let (new_sp, should_balance) := delete' sk sp in
  			      let new_node := (bptNode b X new_sp nil) in
  			        balance (new_node, should_balance)
  			    
  | bptNode sp ((k, child) :: xs) => 
                if blt_nat sk k 
  			    then 
  			      let (new_sp, should_balance) := delete' sk sp in
  			      let new_node := (bptNode b X new_sp ((k, child) :: xs)) in
  			        balance (new_node, should_balance)
  			    
  			    else 
  			      let (new_node_list, should_balance) := traverse_node ((k, child) :: xs) in
  			      let new_node := (bptNode b X sp (new_node_list)) in
  			        balance (new_node, should_balance)
  end.

Definition delete {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X))
                : bplustree b X :=
  match fst (delete' sk tree) with
  | bptNode sp nil => sp
  | t => t 
  end.
  
Definition empty2Tree := bptLeaf 1 nat [].
Definition atree:= insert 17 117 (insert 6 106 (insert 31 131 (insert 4 104 (insert 20 120 (insert 15 115 
                   (insert 1 101 (insert 7 107 (insert 3 103 empty2Tree)))))))).
Eval compute in atree.

(*Definition missing_some := delete 31 (delete 20 (delete 6 (delete 3 (delete 4 atree)))).
Eval compute in missing_some.
Definition missing_17 := delete 17 missing_some.
Eval compute in delete 15 (delete 7 (delete 1 missing_17)).*)

  
  
  *)
  
  
  
  
  
  
  
  
  
