Require Export SfLib.
Require Export HelperFunctions.

Inductive bplustree (b: nat) (X:Type) : Type :=
  | bptLeaf : list (nat * X) -> bplustree b X
  | bptNode : list (nat * (bplustree b X)) -> bplustree b X
  . 

Notation "[[ b , X | x , .. , y ]]" := (bptLeaf b X (cons x .. (cons y []) ..)) (at level 100, format 
  "[[ b , X | '[v ' x , .. , y ']' ]]").
Notation "{{ b , X | f , x , .. , y }}" := (bptNode b X f (cons x .. (cons y []) ..)) (at level 99, format
  "{{ b , X | '[v  ' '//' f , '//' x , .. , y ']' '//' }}").

Example test := bptLeaf 2 bool [(1, true), (2, false)].


Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall k v l, appears_in_kvl sk l -> appears_in_kvl sk ((k, v)::l).
  
Inductive appears_in_tree {X:Type} {b: nat} (sk: nat) : bplustree b X -> Prop :=
  | ait_leaf       : forall l,       appears_in_kvl sk l -> appears_in_tree sk (bptLeaf b X l)
  | ait_node_one   : forall k v,     appears_in_tree sk v -> k <= sk ->
                                     appears_in_tree sk (bptNode b X [(k, v)])
  | ait_node_here  : forall k1 k2 v1 v2 l, 
                                     appears_in_tree sk v1 -> k1 <= sk /\ sk < k2 ->
                                     appears_in_tree sk (bptNode b X ((k1, v1)::(k2, v2)::l))
  | ait_node_later : forall x k v l, appears_in_tree sk (bptNode b X ((k, v)::l)) -> k <= sk ->
                                     appears_in_tree sk (bptNode b X (x::(k, v)::l)).
  
  
Inductive kvl_sorted {X: Type}: list (nat * X) -> Prop :=
  kvl_sorted_0    : kvl_sorted []
| kvl_sorted_1    : forall (n: nat) (x: X), 
                      kvl_sorted [(n, x)]
| kvl_sorted_cons : forall (n1 n2: nat) (x1 x2: X) (lst: list (nat * X)), 
                      kvl_sorted ((n2,x2)::lst) -> blt_nat n1 n2 = true
                       -> kvl_sorted ((n1,x1)::(n2,x2)::lst) 
.