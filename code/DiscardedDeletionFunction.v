(* Deletion *)
(*
 * This deletion function was written in the beginning with the start pointer
 * data structure. It was tested to work but nothing was ever proved about it
 * due to time constraints.
 *)
(*
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
  
  
  
  
  
  
  
  
  
