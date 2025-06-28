Theorem thm0: 
forall a : nat, eq (Nat.add a O) a.
Proof.
intros a. induction a IHa. simpl. simpl. reflexivity. rewrite IHa. custom0. 
Qed.

Theorem thm1: 
forall a : algb, eq (algb_add a e) a.
Proof.
intros a. destruct a H H. custom0. reflexivity. 
Qed.