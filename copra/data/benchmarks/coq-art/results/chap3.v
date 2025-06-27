Theorem imp_trans : ( P -> Q ) -> ( Q -> R ) -> P -> R .
Proof.
   custom1 H H' p.
Qed.
Theorem imp_trans' : ( P -> Q ) -> ( Q -> R ) -> P -> R .
Proof.
   custom1 H H' p.
Qed.
Lemma apply_example : ( Q -> R -> T ) -> ( P -> Q ) -> P -> R -> T .
Proof.
   intros H H0 p. apply H. exact ( H0 p ).
Qed.
Theorem imp_dist : ( P -> Q -> R ) -> ( P -> Q ) -> ( P -> R ) .
Proof.
   custom2 H H' p.
Qed.
Theorem K : P -> Q -> P .
Proof.
   intros p q. assumption.
Qed.
Theorem triple_impl_one_liner : ( ( ( P -> Q ) -> Q ) -> Q ) -> P -> Q .
Proof.
   intros H p. apply H. intro H0. custom0 H0.
Qed.
Lemma imp_dist' : ( P -> Q -> R ) -> ( P -> Q ) -> ( P -> R ) .
Proof.
   custom2 H H' p.
Qed.
Lemma assert_example : Q .
Proof.
   assert ( H3 : P -> R ).
    - intro p. apply H0. custom0 H.
    - custom0 H1. custom0 H2.
Qed.

Ltac custom0 H0 :=  apply H0; [assumption | .. ].
Ltac custom1 H0 H1 H2 :=  intros H0 H1 H2; [apply H1; [custom0  | .. ] | .. ].
Ltac custom2 H0 H1 H2 :=  intros H0 H1 H2; [custom0 ; [custom0  | .. ] | .. ].
