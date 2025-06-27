Theorem zero_cons_ord : forall l : list nat, sorted le l -> sorted le ( cons 0 l ) .
Proof.
   induction 1.
    - auto with sorted_base arith.
    - auto with sorted_base arith.
    - auto with sorted_base arith.
Qed.
Theorem sorted1_inv { A : Type } { le : relation A } { x l } ( H : sorted le ( x :: l ) ) : sorted le l .
Proof.
   inversion H.
    - auto with sorted_base.
    - auto with sorted_base.
Qed.
Theorem sorted2_inv { A : Type } { le : relation A } { x y l } ( H : sorted le ( x :: y :: l ) ) : le x y .
Proof.
   inversion H. auto with sorted_base.
Qed.
Theorem not_sorted_132 : ~ sorted le ( 1 :: 3 :: 2 :: nil ) .
Proof.
   intros H. generalize ( sorted1_inv H ). intro H0. generalize ( sorted2_inv H0 ). lia.
Qed.
Theorem any_height_inj2 { A : Type } : forall ( n1 n2 : nat ) ( t1 : htree A n1 ) ( t2 : htree A n2 ), any_height n1 t1 = any_height n2 t2 -> JMeq t1 t2 .
Proof.
   custom3 n1 n2 t1 t2 H. dependent rewrite <- H1. trivial.
Qed.
Theorem any_height_inj2' { A : Type } : forall ( n1 n2 : nat ) ( t1 : htree A n1 ) ( t2 : htree A n2 ), any_height n1 t1 = any_height n2 t2 -> JMeq t1 t2 .
Proof.
   intros n1 n2 t1 t2 H. change ( match any_height n2 t2 with | any_height n t => JMeq t1 t end ). now rewrite <- H.
Qed.
Theorem keep_length : forall ( n : nat ) ( v : t A n ), length ( vector_to_list n v ) = n .
Proof.
   intros n v. induction v.
    - custom0.
    - custom0.
Qed.
Lemma Vconseq : forall ( a : A ) ( n m : nat ), n = m -> forall ( v : t A n ) ( w : t A m ), JMeq v w -> JMeq ( cons A a n v ) ( cons A a m w ) .
Proof.
   intros a n m Heq. rewrite Heq. intros v w HJeq. rewrite HJeq. reflexivity.
Qed.
Theorem vect_to_list_and_back : forall n ( v : t A n ), JMeq v ( list_to_vector ( vector_to_list n v ) ) .
Proof.
   intros n v. induction v as [ | h n v IHv ].
    - reflexivity.
    - simpl. apply Vconseq.
      -- now rewrite keep_length.
      -- assumption.
Qed.
Theorem structured_intro_example1 : forall A B C : Prop, A /\ B /\ C -> A .
Proof.
   intros A B C [ Ha [ Hb Hc ] ]. assumption.
Qed.
Theorem structured_intro_example2 : forall A B : Prop, A \/ B /\ ( B -> A ) -> A .
Proof.
   intros A B [ Hb | [ Hi A ] ].
    - assumption.
    - now apply Hi.
Qed.
Theorem sum_even : forall n p : nat, even n -> even p -> even ( n + p ) .
Proof.
   intros n p Heven_n. induction Heven_n.
    - trivial.
    - intro H0. simpl. constructor. auto.
Qed.
Theorem lt_le : forall n p : nat, n < p -> n <= p .
Proof.
   intros n p H. induction H.
    - repeat constructor.
    - repeat constructor. assumption.
Qed.
Theorem pfact3 : Pfact 3 6 .
Proof.
   apply Pfact1 with ( n := 3 ) ( v := 2 ).
    - discriminate.
    - apply ( Pfact1 2 1 ).
      -- discriminate.
      -- apply ( Pfact1 1 1 ).
        --- discriminate.
        --- apply Pfact0.
Qed.
Theorem fact_def_pos : forall x y : Z, Pfact x y -> 0 <= x .
Proof.
   intros x y H. induction H.
    - auto with zarith.
    - lia.
Qed.
Theorem Zle_Pfact : forall x : Z, 0 <= x -> exists y : Z, Pfact x y .
Proof.
   intros x. induction x using ( well_founded_ind ( Zwf_well_founded 0 ) ). intros Hle. destruct ( Zle_lt_or_eq _ _ Hle ) as [  H0 | H0 ].
    - destruct ( H ( x - 1 ) ) as [  | | H1 x0 ].
      -- unfold Zwf. lia.
      -- lia.
      -- exists ( x * x0 ). apply Pfact1.
        --- auto with zarith.
        --- auto with zarith.
    - subst x. exists 1. constructor.
Qed.
Theorem HoareWhileRule : forall ( P : state -> Prop ) ( b : bExp ) ( i : inst ) ( s s' : state ), ( forall s1 s2 : state, P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2 ) -> P s -> exec s ( WhileDo b i ) s' -> P s' /\ evalB s' b = Some false .
Proof.
   intros P b i s s' H. cut ( forall i' : inst, exec s i' s' -> i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false ).
    - eauto.
    - intros i' Hexec. elim Hexec.
      -- try ( intros ; discriminate ).
      -- try ( intros ; discriminate ).
      -- try ( intros ; discriminate ).
      -- custom3 s0 i0 e Heval Heq. rewrite <- H2. auto.
      -- intros s0 s1 s2 i0 e H0 H1 H2 H3 H4 H5 H6. custom1 H5 H' H''. subst i0 b. eauto.
Qed.
Lemma sqr_01 : forall x : nat, is_0_1 x -> is_0_1 ( x * x ) .
Proof.
   induction 1.
    - custom0.
    - custom0.
Qed.
Theorem elim_example : forall n : nat, n <= 1 -> n * n <= 1 .
Proof.
   intros n H. destruct ( sqr_01 n ) as [  | | ].
    - custom2 H. custom2 H0.
    - auto.
    - auto.
Qed.
Theorem not_even_1 : ~ even 1 .
Proof.
   unfold not. intros H. inversion H.
Qed.
Theorem plus_2_even_inv : forall n : nat, even ( S ( S n ) ) -> even n .
Proof.
   intros n H. inversion H. assumption.
Qed.
Theorem not_even_1' : ~ even 1 .
Proof.
   intro H. generalize ( refl_equal 1 ). pattern 1 at - 2. induction H.
    - discriminate.
    - discriminate.
Qed.
Theorem plus_2_even_inv' : forall n : nat, even ( S ( S n ) ) -> even n .
Proof.
   intros n H. generalize ( refl_equal ( S ( S n ) ) ). pattern ( S ( S n ) ) at - 2. induction H.
    - discriminate.
    - intros H0. injection H0. intro H1.
Qed.


Ltac custom0  :=  simpl; [auto | .. ].
Ltac custom1 H0 H1 H2 :=  injection H0; [intros H1 H2 | .. ].
Ltac custom2 H0 :=  inversion_clear H0; [auto |  | .. ].
Ltac custom3 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [custom1  | .. ].
