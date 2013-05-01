Require Export SfLib.

Fixpoint cut_list_left {X: Type} (b: nat) (lst: list X) : list X :=
  match b with
  | O => nil
  | S b' => match lst with
            | nil => nil
            | x::lst' => x :: (cut_list_left b' lst')
    end
  end. 
  
Fixpoint cut_list_right {X: Type} (b: nat) (lst: list X) : list X :=
  match b with
  | 0 => lst
  | S b' => match lst with
            | nil => lst
            | _ :: lst' => cut_list_right b' lst'
            end
  end.
  
Definition split_list {X: Type} (b: nat) (lst: list X) : (list X * list X) :=
  (cut_list_left b lst, cut_list_right b lst).

Definition alist := [0,1,2,3,4,5,6].
Definition ab := 9.
Eval compute in split_list ab alist.
  
Lemma cons_remove : forall (X: Type) (x: X) (l1 l2: list X),
  x :: l1 = x :: l2 <-> l1 = l2.
Proof.
  intros X x. induction l1; intros; split; intros; inversion H; reflexivity.
Qed.
  
Lemma cut_list_left_add_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  cut_list_left (S b) (x :: l) = x :: cut_list_left b l.
Proof.
  intros X x b. induction b. intros. compute. reflexivity.
  intros. destruct l. reflexivity. simpl. reflexivity.
Qed.


Lemma cut_list_right_remove_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  cut_list_right (S b) (x :: l) = cut_list_right b l.
Proof.
  intros X x b. induction b. intros. reflexivity.
  intros. destruct l. reflexivity.
  simpl. reflexivity.
Qed.
  
Lemma cut_list_add_remove_one : forall (X: Type) (x: X) (b: nat) (l: list X),
  x :: l = x :: (cut_list_left b l ++ cut_list_right b l) ->
  x :: l = cut_list_left (S b) (x :: l) ++ cut_list_right (S b) (x :: l).
Proof.
  intros X x b. induction b; intros.
  Case "b = 0".
    compute. reflexivity.
  Case "b = S b".
   intros. rewrite cut_list_left_add_one. rewrite cut_list_right_remove_one. apply H. 
Qed.

  
Theorem cut_list_left_right_preserves_list : forall (X: Type) (b: nat) (l: list X),
  l = (cut_list_left b l) ++ (cut_list_right b l).
Proof.
  intros X b. induction b. intros. compute. reflexivity.
  intros. destruct l. compute. reflexivity. 
  apply cut_list_add_remove_one. apply cons_remove. apply IHb.
Qed.

  
Theorem split_list_preserves_lists : forall (X: Type) (b: nat) (l l1 l2: list X),
  split_list b l = (l1, l2) -> l = l1 ++ l2.
Proof.
  intros X b. induction b. intros. compute in H. inversion H. reflexivity.
  intros. unfold split_list in H. destruct l. inversion H. reflexivity.
  rewrite cut_list_right_remove_one in H. rewrite cut_list_left_add_one in H.
  inversion H. rewrite <- app_comm_cons. apply cons_remove. apply cut_list_left_right_preserves_list.
Qed.  
    