Require Export SfLib.

Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.

Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptNode : bplustree b X -> list (nat * (bplustree b X)) -> bplustree b X
  | bptLeaf : list (nat * X) -> bplustree b X
  . 


Example test := bptLeaf 2 bool [(1, true), (2, false)].


Definition head {X: Type} {b: nat} (kpl: (list (nat * bplustree b X))) : option nat :=
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


Definition left := bptLeaf 2 nat [(4, 44), (5, 55)].
Definition centre := bptLeaf 2 nat [(7, 77)].
Definition right := bptLeaf 2 nat [(9, 99)].
Definition root := bptNode 2 nat left [(peek centre, centre), (peek right, right)].

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


Example search_test_find_item_left : search 4 root = Some 44.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_centre : search 7 root = Some 77.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 9 root = Some 99.
Proof. simpl. reflexivity. Qed.
Example search_test_cant_find_missing : search 6 root = None.
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
  
Fixpoint insert {X: Type} {b: nat} (sk: nat) (v: X) (tree: (bplustree b X))
                : (bplustree b X * option (bplustree b X)) :=

  (* More or less copy-pasted from search *)
  let fix split_if_necessary (input: (bplustree b X * option (bplustree b X)))
  							: (bplustree b X * option (bplustree b X)) :=
  							match input with
  							  | (tree, None) => (tree, None)
  							  | (tree, Some new) => (tree, Some new)
  							end
  in 
  let fix insert_into_node
                      (kpl: (list (nat * bplustree b X)))
                   : (bplustree b X * option (bplustree b X)) :=
    match kpl with
      | nil => (tree, None)
      | (k, p) :: kpl' => match head kpl' with
        | None => split_if_necessary (insert k v p)
        | Some k' => if andb (ble_nat k sk) (blt_nat sk k')
      						then split_if_necessary (insert k v p)
      						else insert_into_node kpl'
       end
     end 
     
  in 
  match tree with
    | bptLeaf kvl => let (fst, snd_opt) := insert_leaf b sk v kvl in
                     match snd_opt with
                       | None => (bptLeaf b X fst, None)
                       | Some snd => (bptLeaf b X fst, Some (bptLeaf b X snd))
                     end 
    | bptNode sp kpl => match head kpl with
      | None => (tree, None)
      | Some k => if blt_nat sk k
      	then split_if_necessary (insert k v sp)
      	else insert_into_node kpl
    end
  end.
  
