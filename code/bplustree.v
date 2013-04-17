Require Export SfLib.
Require Export helper_proofs.

Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptNode : bplustree b X -> list (nat * (bplustree b X)) -> bplustree b X
  | bptLeaf : list (nat * X) -> bplustree b X
  . 

Notation "[[ b , X | x , .. , y ]]" := (bptLeaf b X (cons x .. (cons y []) ..)) (at level 100, format 
  "[[ b , X | '[v ' x , .. , y ']' ]]").
Notation "{{ b , X | f , x , .. , y }}" := (bptNode b X f (cons x .. (cons y []) ..)) (at level 99, format
  "{{ b , X | '[v  ' '//' f , '//' x , .. , y ']' '//' }}").

Example test := bptLeaf 2 bool [(1, true), (2, false)].


Definition head_key {X: Type} (kpl: (list (nat * X))) : option nat :=
  match kpl with
    | nil => None
    | (k, v) :: kvl' => Some k
  end.
  
Definition peek_key {X: Type} {b: nat} (tree: (bplustree b X)) : nat :=
  match tree with
    | bptLeaf nil => 0
    | bptLeaf (x :: _) => fst x
    | bptNode sp kpl => match head_key kpl with
      | Some k => k
      | None => 0
      end
  end. 
  
Fixpoint peek_key_deep {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  match tree with
  | bptLeaf nil => 0
  | bptLeaf (x :: _) => fst x
  | bptNode sp _ => peek_key_deep sp
  end.

Definition left := bptLeaf 1 nat [(5, 55)].
Definition centre := bptLeaf 1 nat [(7, 77)].
Definition right := bptLeaf 1 nat [(9, 99)].
Definition root := bptNode 1 nat left [(peek_key centre, centre), (peek_key right, right)].

Fixpoint search_leaf {X: Type} (sk: nat) (kvl: (list (nat * X))) : option X :=
  match kvl with
    | nil => None
    | (k, v) :: kvl' => if beq_nat k sk then Some v else search_leaf sk kvl'
  end.

Fixpoint find_child {X: Type} {b: nat} (sk: nat) (sp: (bplustree b X)) (kpl: (list (nat * bplustree b X))) : option (bplustree b X) :=
  let fix find_child' (kpl: (list (nat * bplustree b X))) : option (bplustree b X) :=
    match kpl with
      | nil => None
      | (k, p) :: kpl' => match head_key kpl' with
        | None => Some p
        | Some k' => if andb (ble_nat k sk) (blt_nat sk k')
      						then Some p
      						else find_child' kpl'
       end
     end 
  in 
  match head_key kpl with
    | None => None
    | Some k => if blt_nat sk k
      then Some sp
      else find_child' kpl
  end.

Fixpoint search {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X)) : option X :=
  let fix search_node
                      (kpl: (list (nat * bplustree b X)))
                   : option X :=
    match kpl with
      | nil => None
      | (k, p) :: kpl' => match head_key kpl' with
        | None => search sk p
        | Some k' => if andb (ble_nat k sk) (blt_nat sk k')
      						then search sk p
      						else search_node kpl'
       end
     end 
  in 
  match tree with
    | bptLeaf kvl => search_leaf sk kvl
    | bptNode sp kpl => match head_key kpl with
      | None => None
      | Some k => if blt_nat sk k
      	then search sk sp
      	else search_node kpl
    end
  end.

Example search_test_find_item_left : search 4 root = None.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_centre : search 7 root = Some 77.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 9 root = Some 99.
Proof. simpl. reflexivity. Qed.
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
    | bptNode sp kpl => (all_members sp) ++ (node_members kpl)
  end.

Example all_members_left : all_members left = [(5, 55)].
Proof. simpl. reflexivity. Qed.
Example all_members_root : all_members root = [(5, 55), (7, 77), (9, 99)].
Proof. simpl. reflexivity. Qed.

Fixpoint insert_into_list {X: Type} (k: nat) (v: X) (kvl: list (nat * X)) : list (nat * X) :=
  match kvl with 
    | nil => [(k, v)]
    | (k', v') :: kvl' => if ble_nat k k'
    						then if beq_nat k k' then ((k, v) :: kvl') else ((k, v) :: kvl)
    						else (k', v') :: (insert_into_list k v kvl')
  end.

Inductive kvl_sorted {X: Type}: list (nat * X) -> Prop :=
  kvl_sorted_0    : kvl_sorted []
| kvl_sorted_1    : forall (n: nat) (x: X), 
                      kvl_sorted [(n, x)]
| kvl_sorted_cons : forall (n1 n2: nat) (x1 x2: X) (lst: list (nat * X)), 
                      kvl_sorted ((n2,x2)::lst) -> blt_nat n1 n2 = true
                       -> kvl_sorted ((n1,x1)::(n2,x2)::lst) 
.


Fixpoint split_list' {X: Type} (b: nat) (fst snd: list X) : (list X * list X) :=
  match b with
    | O => (rev fst, snd)
    | S b' => match snd with
      | nil => (rev fst, snd)
      | f::snd' => split_list' b' (f::fst) snd'
    end
  end. 
Definition split_list {X: Type} (b: nat) (lst: list X) : (list X * list X) :=
  split_list' b [] lst.

Definition insert_leaf {X: Type} (b: nat) (k: nat) (v: X) (kvl: list (nat * X))
						: (list (nat * X) * option (list (nat * X))) :=
  let
  	kvl' := insert_into_list k v kvl
  in
    if ble_nat (length kvl') (mult b 2)
      then (kvl', None)
      else let (fst, snd) := split_list b kvl' in (fst, Some snd) 
  .
  
(*  
Fixpoint insert {X: Type} {b: nat} (sk: nat) (v: X) (tree: (bplustree b X))
              : (bplustree b X * option (bplustree b X)) := 
  match tree with
    | bptLeaf kvl => let (fst, snd_opt) := insert_leaf b sk v kvl in
                     match snd_opt with
                       | None => (bptLeaf b X fst, None)
                       | Some snd => (bptLeaf b X fst, Some (bptLeaf b X snd))
                     end
    | bptNode sp kpl => match find_child sk sp kpl with
      | None => (tree, None)
      | Some p => insert sk v p
    end
  end.
*)

Definition split_if_necessary {X: Type} {b: nat} (tree: (bplustree b X))
  							: (bplustree b X * option (nat * bplustree b X)) := 
  match tree with
  	| bptLeaf kvl => (tree, None)
  	| bptNode sp kpl => if ble_nat (length kpl) (mult b 2)
      then (tree, None)
      else let 
        (fst, snd) := split_list b kpl
      in match snd with
        | nil => (tree, None)
        | (k', sp')::snd' => (bptNode b X sp fst, Some (k', bptNode b X sp' snd'))
      end
  end. 

Definition insert_node {X: Type} {b: nat} (key: option nat) (tree: (bplustree b X)) (input: (bplustree b X * option (nat * bplustree b X)))
  							: (bplustree b X * option (nat * bplustree b X)) :=
  match tree with
  	| bptLeaf kvl => input
  	| bptNode sp kpl =>	match key with
      (* Replace start-pointer *)
  	  | None => match input with
  	    (* No new child-node, just replace start-pointer *)
  	    | (tree, None) => (bptNode b X tree kpl, None)
  		| (tree, Some (new_key, new)) => split_if_necessary (bptNode b X tree (insert_into_list new_key new kpl))
  	  end
  	  (* Replace the pointer with key = k *)
  	  | Some k => match input with
        | (tree, None) => (bptNode b X sp (insert_into_list k tree kpl), None)
  		| (tree, Some (new_key, new)) => split_if_necessary (bptNode b X sp (insert_into_list k tree (insert_into_list new_key new kpl)))
  	  end
    end
  end.
  
  
Fixpoint insert' {X: Type} {b: nat} (insert_key: nat) (v: X) (tree: (bplustree b X))
                : (bplustree b X * option (nat * bplustree b X)) :=

  (* More or less copy-pasted from search *)
  let fix insert_into_node
                      (kpl: (list (nat * bplustree b X)))
                   : (bplustree b X * option (nat * bplustree b X)) :=
    match kpl with
      | nil => (tree, None)
      | (k, p) :: kpl' => match head_key kpl' with
        | None => insert_node (Some k) tree (insert' insert_key v p)
        | Some k' => if andb (ble_nat k insert_key) (blt_nat insert_key k')
      						then insert_node (Some k) tree (insert' insert_key v p)
      						else insert_into_node kpl'
       end
     end 
     
  in 
  match tree with
    | bptLeaf kvl => let (fst, snd_opt) := insert_leaf b insert_key v kvl in
                     match snd_opt with
                       | None => (bptLeaf b X fst, None)
                       | Some snd => match head_key snd with
                         | None => (bptLeaf b X fst, None)
                         | Some first_key => (bptLeaf b X fst, Some (first_key, bptLeaf b X snd))
                         end
                     end 
    | bptNode sp kpl => match head_key kpl with
      | None => (tree, None)
      | Some k => if blt_nat insert_key k
      	then insert_node None tree (insert' insert_key v sp)
      	else insert_into_node kpl
    end
  end.

Definition insert {X: Type} {b: nat} (insert_key: nat) (v: X) (tree: (bplustree b X))
                : bplustree b X :=
  match insert' insert_key v tree with
    | (tree, None) => tree
    | (left, Some (key, right)) => bptNode b X left [(key, right)]
  end.

Eval compute in (root).
Eval compute in (insert 1 11 left).
Eval compute in (insert 3 33 (insert 2 22 (insert 6 66 (insert 1 11 root)))).  



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
    | bptNode sp kvl => max_nat (height' (S h) sp) ((S h) + (highest_in_list 0 kvl))
  end.

Definition height {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  height' 0 tree.
  
Example height_1 : height root = 1.
Proof. simpl. reflexivity. Qed.
Example height_2 : height (bptNode 1 nat (bptNode 1 nat (bptLeaf 1 nat [(1, 11)]) []) []) = 2.
Proof. simpl. reflexivity. Qed.
Example height_3 : height (bptNode 1 nat (bptNode 1 nat (bptNode 1 nat (bptLeaf 1 nat [(1, 11)]) []) []) []) = 3.
Proof. simpl. reflexivity. Qed. 
Eval compute in (height (bptNode 1 nat (bptLeaf 1 nat [(4, 44)]) [((1, bptNode 1 nat (bptNode 1 nat (bptLeaf 1 nat [(1, 11)]) []) []))])).
Example height_right_4 : height (bptNode 1 nat (bptLeaf 1 nat [(1, 11)]) [((4, bptNode 1 nat (bptNode 1 nat (bptLeaf 1 nat [(4, 11)]) []) []))]) = 3.
Proof. compute. reflexivity. Qed.



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
    | bptNode sp kvl => min_nat (mindepth' (S h) sp) ((S h) + (lowest_in_list (height sp) kvl))
  end.
  
Definition mindepth {X: Type} {b: nat} (tree: bplustree b X) : nat :=
  mindepth' 0 tree.

Definition mindepth_tree := (bptNode 1 nat (bptLeaf 1 nat [(11, 1)]) [(22, bptNode 1 nat (bptNode 1 nat (bptLeaf 1 nat [(33, 3)]) []) [])]).
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
Example list2bplustree_4 : list2bplustree 1 [(4, 4), (2, 2), (3, 3), (1, 1)] = bptNode 1 nat (bptLeaf 1 nat [(1, 1), (2, 2)]) [(3, (bptLeaf 1 nat [(3, 3), (4, 4)]))].
Proof. compute. reflexivity. Qed.

Eval compute in ({{1, nat | [[1, nat | (1, 11)]], (22, [[1, nat | (2, 22)]])}}).
Eval compute in (list2bplustree 1 [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]).

Definition bigtree := list2bplustree 1 [(11, 1), (22, 2), (33, 3), (44, 4), (55, 5), (66, 6), (77, 7)].

Eval compute in (bigtree).
Eval compute in (height bigtree).
Eval compute in (mindepth' 0 bigtree).



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

  
  
  
  
  
  
  
  
  
  
  
  
