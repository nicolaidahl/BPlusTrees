Require Export SfLib.

Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.

Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptNode : bplustree b X -> list (nat * (bplustree b X)) -> bplustree b X
  | bptLeaf : list (nat * X) -> bplustree b X
  . 


Example test := bptLeaf 2 bool [(1, true), (2, false)].


Definition head {X: Type} (kpl: (list (nat * X))) : option nat :=
  match kpl with
    | nil => None
    | (k, v) :: kvl' => Some k
  end.
  
Definition peek {X: Type} {b: nat} (tree: (bplustree b X)) : nat :=
  match tree with
    | bptLeaf kvl => match kvl with
      | nil => 0
      | (k,v) :: kvl' => k
      end
    | bptNode sp kpl => match head kpl with
      | Some k => k
      | None => 0
      end
  end. 

Definition left := bptLeaf 1 nat [(5, 55)].
Definition centre := bptLeaf 1 nat [(7, 77)].
Definition right := bptLeaf 1 nat [(9, 99)].
Definition root := bptNode 1 nat left [(peek centre, centre), (peek right, right)].

Fixpoint search_leaf {X: Type} (sk: nat) (kvl: (list (nat * X))) : option X :=
  match kvl with
    | nil => None
    | (k, v) :: kvl' => if beq_nat k sk then Some v else search_leaf sk kvl'
  end.

Fixpoint find_child {X: Type} {b: nat} (sk: nat) (sp: (bplustree b X)) (kpl: (list (nat * bplustree b X))) : option (bplustree b X) :=
  let fix find_child' (kpl: (list (nat * bplustree b X))) : option (bplustree b X) :=
    match kpl with
      | nil => None
      | (k, p) :: kpl' => match head kpl' with
        | None => Some p
        | Some k' => if andb (ble_nat k sk) (blt_nat sk k')
      						then Some p
      						else find_child' kpl'
       end
     end 
  in 
  match head kpl with
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
      | (k, p) :: kpl' => match head kpl' with
        | None => search sk p
        | Some k' => if andb (ble_nat k sk) (blt_nat sk k')
      						then search sk p
      						else search_node kpl'
       end
     end 
  in 
  match tree with
    | bptLeaf kvl => search_leaf sk kvl
    | bptNode sp kpl => match head kpl with
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
      | (k, p) :: kpl' => match head kpl' with
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
                       | Some snd => match head snd with
                         | None => (bptLeaf b X fst, None)
                         | Some first_key => (bptLeaf b X fst, Some (first_key, bptLeaf b X snd))
                         end
                     end 
    | bptNode sp kpl => match head kpl with
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
 
(* Deletion *)
Fixpoint delete_from_list {X: Type} (sk: nat) (lst: list (nat * X))
                          : list (nat * X) :=
  match lst with
  | nil => nil
  | (k, v) :: xs => if beq_nat k sk 
                    then xs 
                    else (k,v) :: delete_from_list sk xs  
  end.

              
Fixpoint delete {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X))
                : bplustree b X :=
  
  let fix traverse_node (nptrs: list (nat * (bplustree b X)))
                   : list (nat * (bplustree b X)) :=
    match nptrs with
    | nil => nil
    | (k1,t1) :: xs => match xs with
                       | nil => [(k1, delete sk t1)]
                       | (k2, t2) :: xs' => if blt_nat sk k2 
                                            then (k1, (delete sk t1)) :: xs
                                            else (k1,t1) :: traverse_node xs
                       end
    end
  
  in
  
  match tree with
  | bptLeaf kvl => bptLeaf b X (delete_from_list sk kvl)
  | bptNode sp nil => delete sk sp
  | bptNode sp ((k, child) :: xs) => 
                if blt_nat sk k 
  			    then bptNode b X (delete sk sp) ((k, child) :: xs)
  			    else bptNode b X sp (traverse_node ((k, child) :: xs)) 
  end.
  
Eval compute in root.
Eval compute in delete 7 root.
  
