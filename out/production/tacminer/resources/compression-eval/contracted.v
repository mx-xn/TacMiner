Theorem thm0: 
forall a : nat, eq (Nat.add a O) a.
Proof.
intros a. induction a IHa. simpl. simpl. custom0. rewrite IHa. 
Qed.

Theorem thm1: 
forall a : algb, eq (algb_add a e) a.
Proof.
intros a. destruct a H H. custom0. 
Qed.