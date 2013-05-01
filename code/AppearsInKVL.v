Require Import HelperFunctions.
Require Import LowLevelHelperProofs.

(* 
 * Proofs about appears In List 
 *)

Inductive appears_in_kvl {X:Type} (sk: nat) : list (nat * X) -> Prop :=
  | ai_here : forall v l, appears_in_kvl sk ((sk, v)::l)
  | ai_later : forall k v l, appears_in_kvl sk l -> appears_in_kvl sk ((k, v)::l).

Lemma element_at_index_impl_appears: forall (X: Type) (b k: nat) (v: X) (l: list (nat*X)),
  element_at_index b l = Some (k, v) -> appears_in_kvl k l.
Proof.
  intro X. induction b; intros; destruct l; inversion H; destruct p.
  Case "b = 0".
     inversion H. apply ai_here.
  Case "b = S b".
    apply ai_later. apply IHb with (v:=v). inversion H. reflexivity.
Qed.

Lemma appears_in_kvl_app : forall (X: Type) (k: nat) (l: list (nat*X)),
  appears_in_kvl k l -> exists l1, exists l2, exists v, l = l1++(k,v)::l2.
Proof.
  intros X k l H. induction H. exists []. exists l. exists v. reflexivity.
  inversion IHappears_in_kvl. inversion H0. inversion H1.
  exists ((k0, v)::witness). exists witness0. exists witness1. simpl. rewrite cons_remove. apply H2.
Qed.