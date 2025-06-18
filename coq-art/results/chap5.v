Ltac custom0 H0 :=  apply H0; [assumption | .. ].
Ltac custom1 H0 H1 :=  unfold H0; [apply H1 | .. ].
Ltac custom2 H0 H1 :=  intros H0 H1; [assumption | .. ].

Theorem conv_example : forall n : nat, 7 * 5 < n -> 6 * 6 <= n .
Proof.
   custom2 n H.
Qed.
Theorem imp_trans : forall P Q R : Prop, ( P -> Q ) -> ( Q -> R ) -> P -> R .
Proof.
   intros P Q R H H0 p. apply H0. custom0 H.
Qed.
Lemma one_neutral_left : neutral_left Z Zmult 1 % Z .
Proof.
   intro z. ring.
Qed.
Lemma le_i_SSi : forall i : nat, i <= S ( S i ) .
Proof.
   intro i. do 2 apply le_S. apply le_n.
Qed.
Lemma all_imp_dist : forall ( A : Type ) ( P Q : A -> Prop ), ( forall x : A, P x -> Q x ) -> ( forall y : A, P y ) -> forall z : A, Q z .
Proof.
   intros A P Q H H0 z. apply H. apply H0.
Qed.
Lemma mult_le_compat_r : forall m n p : nat, le n p -> le ( n * m ) ( p * m ) .
Proof.
   intros m n p H. rewrite ( Nat.mul_comm n m ). rewrite ( Nat.mul_comm p m ). custom0 Nat.mul_le_mono_l.
Qed.
Lemma le_mult_mult : forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d .
Proof.
   intros a b c d H H0. apply Nat.le_trans with ( m := c * b ).
    - custom0 mult_le_compat_r.
    - custom0 Nat.mul_le_mono_l.
Qed.
Lemma le_mult_mult' : forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d .
Proof.
   intros a b c d H H0. eapply Nat.le_trans.
    - eapply Nat.mul_le_mono_l. eexact H0.
    - custom0 mult_le_compat_r.
Qed.
Lemma le_O_mult : forall n p : nat, 0 * n <= 0 * p .
Proof.
   intros n p. apply le_n.
Qed.
Lemma lt_8_9 : 8 < 9 .
Proof.
   custom1 lt le_n.
Qed.
Lemma lt_S : forall n p : nat, n < p -> n < S p .
Proof.
   intros n p H. unfold lt. custom0 le_S.
Qed.
Theorem unfold_example : forall x y : Z, x * x = y * y -> Zsquare_diff x y * Zsquare_diff ( x + y ) ( x * y ) = 0 .
Proof.
   intros x y Heq. unfold Zsquare_diff at 1. rewrite Heq. ring.
Qed.
Lemma ex1 : 220 = 284 .
Proof.
   apply False_ind. exact ff.
Qed.
Theorem absurd : forall P Q : Prop, P -> ~ P -> Q .
Proof.
   intros P Q p H. elim H. assumption.
Qed.
Theorem double_neg_i : forall P : Prop, P -> ~ ~ P .
Proof.
   intros P p H. custom0 H.
Qed.
Theorem modus_ponens : forall P Q : Prop, P -> ( P -> Q ) -> Q .
Proof.
   intros P Q H H0. auto.
Qed.
Theorem double_neg_i' : forall P : Prop, P -> ~ ~ P .
Proof.
   intro P. exact ( modus_ponens P False ).
Qed.
Theorem contrap : forall A B : Prop, ( A -> B ) -> ~ B -> ~ A .
Proof.
   intros A B. custom1 not imp_trans.
Qed.
Theorem disj4_3' : forall P Q R S : Prop, R -> P \/ Q \/ R \/ S .
Proof.
   right. right. left. assumption.
Qed.
Lemma and_commutes : forall A B : Prop, A /\ B -> B /\ A .
Proof.
   intros A B H. destruct H as [  H0 H ]. split.
    - assumption.
    - assumption.
Qed.
Lemma or_commutes : forall A B : Prop, A \/ B -> B \/ A .
Proof.
   intros A B H. destruct H as [ H | H ].
    - auto.
    - auto.
Qed.
Lemma ex_imp_ex : forall ( A : Type ) ( P Q : A -> Prop ), ( ex P ) -> ( forall x : A, P x -> Q x ) -> ( ex Q ) .
Proof.
   intros A P Q H H0. destruct H as [ a Ha ]. exists a. custom0 H0.
Qed.
Lemma diff_of_squares : forall a b : Z, ( ( a + b ) * ( a - b ) = a * a - b * b ) % Z .
Proof.
   intros a b. ring.
Qed.
Theorem eq_sym' : forall ( A : Type ) ( a b : A ), a = b -> b = a .
Proof.
   intros A a b e. rewrite e. reflexivity.
Qed.
Lemma Zmult_distr_1 : forall n x : Z, n * x + x = ( n + 1 ) * x .
Proof.
   intros n x. rewrite Zmult_plus_distr_l. now rewrite Zmult_1_l.
Qed.
Lemma regroup : forall x : Z, x + x + x + x + x = 5 * x .
Proof.
   intro x. pattern x at 1. rewrite <- Zmult_1_l. repeat rewrite Zmult_distr_1. reflexivity.
Qed.
Theorem le_lt_S_eq : forall n p : nat, n <= p -> p < S n -> n = p .
Proof.
   intros n p H H0. lia.
Qed.
Lemma conditional_rewrite_example : forall n : nat, 8 <= n + 6 -> 3 + n < 6 -> n * n = n + n .
Proof.
   intros n H H0. rewrite <- ( le_lt_S_eq 2 n ).
    - reflexivity.
    - apply Nat.add_le_mono_l with ( p := 6 ). rewrite Nat.add_comm in H. auto with arith.
    - apply Nat.add_lt_mono_l with ( p := 3 ). auto with arith.
Qed.
Lemma conditional_rewrite_example' : forall n : nat, 8 <= n + 6 -> 3 + n < 6 -> n * n = n + n .
Proof.
   intros n H H0. assert ( n = 2 ) by lia. now subst n.
Qed.
Theorem eq_trans : forall ( A : Type ) ( x y z : A ), x = y -> y = z -> x = z .
Proof.
   intros A x y z H. rewrite H. auto.
Qed.
Theorem my_I : my_True .
Proof.
   custom2 P p.
Qed.
Theorem my_False_ind : forall P : Prop, my_False -> P .
Proof.
   intros P F. apply F.
Qed.
Theorem leibniz_sym : symmetric A leibniz .
Proof.
   intros x y H Q. apply H. trivial.
Qed.
