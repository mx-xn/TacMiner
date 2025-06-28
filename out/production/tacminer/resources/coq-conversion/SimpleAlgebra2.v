Inductive algb : Set := 
e : algb
| t : algb.

Definition algb_eq (x y : algb) : bool :=
match x, y with
| e, e => true
| t, t => true
| _, _ => false
end.

Definition algb_add (a b : algb) : algb :=
match a, b with
| e, _ => b
| _, e => a
| t, t => e
end.

Definition algb_mul (a b : algb) : algb :=
match a, b with
| e, _ => e
| _, e => e
| t, t => t
end.

Fixpoint algb_mul_scalar (b : nat) (a : algb) : algb :=
match b, a with
| 0, _ => e
| S b', _ => algb_add a (algb_mul_scalar b' a)
end.

Theorem algb_nat_zero : forall a, a 
+ 0 = a.
Proof.
    intros.
    induction a.
    simpl.
    reflexivity.
    simpl.
    rewrite IHa.
    reflexivity.
Qed.

Theorem algb_identity_sum : 
forall a, algb_add a e = a.
Proof.
    intros. 
    destruct (a) eqn:H.
    - reflexivity.
    - reflexivity.
Qed.

Theorem algb_identity_sum2 : 
forall a, algb_add a e = a.
Proof.
    intros. 
    destruct (a) eqn:H.
    - simpl. reflexivity.
    - reflexivity.
Qed.

Theorem algb_identity_sum3 : 
forall a, algb_add a e = a.
Proof.
    intros. 
    destruct (a) eqn:H.
    - simpl in *. reflexivity.
    - reflexivity.
Qed.