Require Export SfLib.


Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptNode : list (nat * (bplustree b X)) -> bplustree b X -> bplustree b X
  | bptLeaf : list (nat * X) -> bplustree b X
  . 


Example test := bptLeaf 2 bool [(1, true), (2, false)].

Definition left := bptLeaf 2 nat [(4, 4), (5, 5)].
Definition centre := bptLeaf 2 nat [(7, 7)].
Definition right := bptLeaf 2 nat [(9, 9)].
Definition root := bptNode 2 nat [(6, left), (8, centre)] right.


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


Example search_test_find_item_left : search 4 root = Some 4.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_centre : search 7 root = Some 7.
Proof. simpl. reflexivity. Qed.
Example search_test_find_item_right : search 9 root = Some 9.
Proof. simpl. reflexivity. Qed.
Example search_test_cant_find_missing : search 6 root = None.
Proof. simpl. reflexivity. Qed.



  
