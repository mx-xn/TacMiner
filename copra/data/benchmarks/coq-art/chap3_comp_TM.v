Section Minimal_propositional_logic.
 Variables P Q R T : Prop.

Ltac custom0 H0 :=  apply H0; [assumption | .. ].
Ltac custom1 H0 H1 H2 :=  intros H0 H1 H2; [apply H1; [custom0 H0 | .. ] | .. ].
Theorem imp_trans : ( P -> Q ) -> ( Q -> R ) -> P -> R .
Proof.
   custom1 H H' p.
Qed.

 
 Theorem imp_trans' : (P->Q)->(Q->R)->P->R.
 Proof.
  intros H H' p. apply H'. apply H. assumption.
 Qed.

 Lemma apply_example : (Q->R->T)->(P->Q)->P->R->T.
 Proof.
  intros H H0 p.
  apply H.
  exact (H0 p).
 Qed.

 Theorem imp_dist : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H.  
  - assumption.
  - apply H'. assumption.
 Qed.

 Theorem K : P->Q->P.
 Proof.
  intros p q. assumption.
 Qed.


 
 Section proof_of_triple_impl.
  Hypothesis H : ((P->Q)->Q)-> Q.
  Hypothesis p : P.

 End proof_of_triple_impl.


 Theorem triple_impl_one_liner : (((P->Q)->Q)->Q)->P->Q.
 Proof.
  intros H p. apply H. intro H0. apply H0. assumption.
 Qed.

 Lemma imp_dist' : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H; [assumption | apply H'; assumption].
 Qed.

 Section section_assert_example.
  Hypotheses (H : P->Q)
             (H0 : Q->R)
             (H1 : (P->R)->T->Q)
             (H2 : (P->R)->T).
 
  Lemma assert_example : Q.
  Proof.
   assert (H3 : P -> R).
   -  intro p; apply H0; apply H; assumption.
   -  apply H1; [assumption | apply H2; assumption].
  Qed.

 Print assert_example.

 End section_assert_example.

End Minimal_propositional_logic.

Print imp_dist.

Section using_imp_dist.
 Variables (P1 P2 P3 : Prop).

 Check imp_dist P1 P2 P3.

 Check imp_dist (P1->P2) (P2->P3) (P3->P1).

End using_imp_dist.