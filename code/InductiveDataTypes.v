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
  | aik_here: forall v l,		appears_in_kvl sk ((sk, v)::l)
  | aik_later: forall k v l,	appears_in_kvl sk l -> appears_in_kvl sk ((k, v)::l).

Inductive kv_appears_in_kvl {X:Type} (sk: nat) (sv: X) : list (nat * X) -> Prop :=
  | kv_aik_here: forall l,		kv_appears_in_kvl sk sv ((sk, sv)::l)
  | kv_aik_later: forall k v l,	kv_appears_in_kvl sk sv l -> kv_appears_in_kvl sk sv ((k, v)::l).
  
Lemma kv_appears_in_kvl_impl_appears_in_kvl: forall (X: Type) (k: nat) (v: X) (l: list (nat * X)),
  kv_appears_in_kvl k v l -> appears_in_kvl k l.
Proof.
  intros.
  induction H; constructor; assumption.
Qed.
  
Inductive appears_in_tree {X:Type} {b: nat} (sk: nat) : bplustree b X -> Prop :=
  | ait_leaf: forall l,	appears_in_kvl sk l -> appears_in_tree sk (bptLeaf b X l)
  | ait_node_last: forall k1 k2 v1 v2, 
		appears_in_tree sk v2 -> k2 <= sk ->
		appears_in_tree sk (bptNode b X [(k1, v1), (k2, v2)])
  | ait_node_here: forall k1 k2 v1 v2 l, 
		appears_in_tree sk v1 -> k1 <= sk /\ sk < k2 ->
		appears_in_tree sk (bptNode b X ((k1, v1)::(k2, v2)::l))
  | ait_node_later: forall x k1 k2 v1 v2 l,
  		appears_in_tree sk (bptNode b X ((k1, v1)::(k2, v2)::l)) -> 
  		k1 <= sk ->
		appears_in_tree sk (bptNode b X (x::(k1, v1)::(k2, v2)::l)).

Inductive kv_appears_in_tree {X:Type} {b: nat} (sk: nat) (sv: X) : bplustree b X -> Prop :=
  | kv_ait_leaf: forall l,	kv_appears_in_kvl sk sv l -> kv_appears_in_tree sk sv (bptLeaf b X l)
  | kv_ait_node_last: forall k1 k2 v1 v2, 
		kv_appears_in_tree sk sv v2 -> k2 <= sk ->
		kv_appears_in_tree sk sv (bptNode b X [(k1, v1), (k2, v2)])
  | kv_ait_node_here: forall k1 k2 v1 v2 l, 
		kv_appears_in_tree sk sv v1 -> k1 <= sk /\ sk < k2 ->
		kv_appears_in_tree sk sv (bptNode b X ((k1, v1)::(k2, v2)::l))
  | kv_ait_node_later: forall x k1 k2 v1 v2 l,
  		kv_appears_in_tree sk sv (bptNode b X ((k1, v1)::(k2, v2)::l)) -> 
  		k1 <= sk ->
		kv_appears_in_tree sk sv (bptNode b X (x::(k1, v1)::(k2, v2)::l)).
  
  
Inductive kvl_sorted {X: Type}: list (nat * X) -> Prop :=
    kvl_sorted_0    : kvl_sorted []
  | kvl_sorted_1    : forall (n: nat) (x: X), 
		kvl_sorted [(n, x)]
  | kvl_sorted_cons : forall (n1 n2: nat) (x1 x2: X) (lst: list (nat * X)), 
		kvl_sorted ((n2,x2)::lst) -> 
		blt_nat n1 n2 = true ->
		kvl_sorted ((n1,x1)::(n2,x2)::lst).
                       
(* Some props for having a prop apply to all elements in a list *)
Inductive all_values (X : Type) (P : X -> Prop) : list (nat * X) -> Prop :=
  | av_empty : all_values X P []
  | av_next : forall (x:X) (n: nat) (l: list (nat * X)), all_values X P l -> P x -> all_values X P ((n,x)::l)
.
Inductive all_keys (X : Type) (P : nat -> Prop) : list (nat * X) -> Prop :=
  | ak_empty : all_keys X P []
  | ak_next : forall (x:X) (n: nat) (l: list (nat * X)), all_keys X P l -> P n -> all_keys X P ((n,x)::l)
.

Inductive all_values_eq_prop (X: Type)(P: X -> X -> Prop) : list (nat * X) -> Prop :=
  | alep_0    : all_values_eq_prop X P []
  | alep_1    : forall (x:X) (n: nat), all_values_eq_prop X P [(n, x)]
  | alep_next : forall (x1 x2:X) (n1 n2: nat) l,  
                  all_values_eq_prop X P ((n2, x2) :: l) -> 
                  P x1 x2 -> 
                  all_values_eq_prop X P ((n1, x1) :: (n2, x2) :: l).

(* Some helper functions for checking if a number is above or below a given number *)
Definition below (n: nat) : nat -> Prop :=
  fun o => blt_nat o n = true. 
Definition below_equal (n: nat) : nat -> Prop :=
  fun o => ble_nat o n = true.
Definition between (n m: nat) : nat -> Prop :=
  fun o => andb (ble_nat n o) (blt_nat o m) = true.
Definition above (m: nat) : nat -> Prop :=
  fun o => ble_nat m o = true.
