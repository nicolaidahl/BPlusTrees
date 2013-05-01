Require Export SfLib.

Lemma cons_remove : forall (X: Type) (x: X) (l1 l2: list X),
  x :: l1 = x :: l2 <-> l1 = l2.
Proof.
  intros X x. induction l1; intros; split; intros; inversion H; reflexivity.
Qed.


Lemma app_one_cons : forall {X: Type} (x: X) l,
  [x] ++ l = x :: l.
Proof. intros. simpl. reflexivity. Qed.