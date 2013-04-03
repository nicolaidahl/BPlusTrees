Require Export SfLib.


Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptNode : list (nat * (bplustree b X)) -> bplustree b X -> bplustree b X
  | bptLeaf : list (nat * X) -> bplustree b X
  . 


  
  
Example test := bptLeaf 2 bool ((1, true)::(2, false)::nil).

Definition left := bptLeaf 2 bool ((4, true)::nil).
Definition right := bptLeaf 2 bool ((6, false)::nil).


Definition root := bptNode 2 bool ((5, left)::nil) right.

Fixpoint search_leaf {X: Type} (sk: nat) (kvl: (list (nat * X))) : option X :=
  match kvl with
    | nil => None
    | (k, v) :: kvl' => if beq_nat k sk then Some v else search_leaf sk kvl'
  end.



Fixpoint search {X: Type} {b: nat} (sk: nat) (tree: (bplustree b X)) : option X :=
  let fix search_node
                      (kpl: (list (nat * bplustree b X)))
                   : option (option X) :=
    match kpl with
      | nil => None
      | (k, p) :: kpl' => if ble_nat sk k then Some (search sk p) else search_node kpl'
    end
  in 
  match tree with
    | bptLeaf kvl => search_leaf sk kvl
    | bptNode kpl ep => match search_node kpl with
      | Some k => k
      | None => search sk ep
    end
  end.


Example search_test_find_item_left : search 4 root = Some true.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 6 root = Some false.
Proof. simpl. reflexivity. Qed.
Example search_test_cant_find_missing : search 5 root = None.
Proof. simpl. reflexivity. Qed.



  
