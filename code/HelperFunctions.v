Require Export SfLib.

(* list *)
Fixpoint element_at_index {X: Type} (n : nat) (lst: list X): option X :=
  match n with
  | 0 => match lst with
         | nil => None
         | x :: _ => Some x
         end
  | S n' => match lst with
            | nil => None
            | _ :: xs => element_at_index n' xs
            end
  end.  


(*
 * blt_nat
 *)

Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.



(*
 * min_nat
 *)
Definition min_nat (n1 n2 : nat) : nat :=
  if ble_nat n1 n2
  then n1
  else n2.
  
Example min_nat_1 : min_nat 1 5 = 1.
Proof. simpl. reflexivity. Qed.
Example min_nat_2 : min_nat 11 3 = 3.
Proof. simpl. reflexivity. Qed.
Example min_nat_3 : min_nat 2 2 = 2.
Proof. simpl. reflexivity. Qed.



(*
 * max_nat
 *)
Definition max_nat (n1 n2 : nat) : nat :=
  if ble_nat n1 n2
  then n2
  else n1.
  
Example max_nat_1 : max_nat 1 5 = 5.
Proof. simpl. reflexivity. Qed.
Example max_nat_2 : max_nat 11 3 = 11.
Proof. simpl. reflexivity. Qed.
Example max_nat_3 : max_nat 2 2 = 2.
Proof. simpl. reflexivity. Qed.
