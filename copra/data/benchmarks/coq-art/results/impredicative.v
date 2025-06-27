Theorem isorted0 : impredicative_sorted nil .
Proof.
   red. intros P H H0 H1. assumption.
Qed.
Theorem isorted1 : forall x : A, impredicative_sorted ( x :: nil ) .
Proof.
   custom2 impredicative_sorted.
Qed.
Theorem isorted2 : forall ( x1 x2 : A ) ( l' : list A ), R x1 x2 -> impredicative_sorted ( x2 :: l' ) -> impredicative_sorted ( x1 :: x2 :: l' ) .
Proof.
   intros x1 x2 l' Hr Hs P Hsn Hs1 Hs2. apply Hs2.
    - auto.
    - custom3.
Qed.
Theorem sorted_to_impredicative_sorted : forall l, sorted l -> impredicative_sorted l .
Proof.
   induction 1.
    - auto.
    - auto.
    - auto.
Qed.
Theorem impredicative_sorted_to_sorted : forall l, impredicative_sorted l -> sorted l .
Proof.
   intros l H. custom3.
Qed.
Theorem impredicative_le_n : forall n : nat, impredicative_le n n .
Proof.
   custom2 impredicative_le.
Qed.
Theorem impredicative_le_S : forall n m : nat, impredicative_le n m -> impredicative_le n ( S m ) .
Proof.
   intros n m Hle P Hn Hs. apply Hs. custom0 Hle.
Qed.
Theorem le_to_impredicative : forall n p, n <= p -> impredicative_le n p .
Proof.
   custom1 n p Hle.
Qed.
Theorem impredicative_to_le : forall n p, impredicative_le n p -> n <= p .
Proof.
   intros n p H. custom0 H.
Qed.
Theorem impredicative_or_intro1 : forall A B : Prop, A -> impredicative_or A B .
Proof.
   custom2 impredicative_or.
Qed.
Theorem impredicative_or_intro2 : forall A B : Prop, B -> impredicative_or A B .
Proof.
   custom2 impredicative_or.
Qed.
Theorem or_to_impredicative : forall A B, A \/ B -> impredicative_or A B .
Proof.
   custom1 A B H.
Qed.
Theorem impredicative_to_or : forall A B, impredicative_or A B -> A \/ B .
Proof.
   intros A B H. custom0 H.
Qed.

Ltac custom0 H0 :=  apply H0; [auto | auto |  | .. ].
Ltac custom1 H0 H1 H2 :=  intros H0 H1 H2; [elim H2; [auto | auto | .. ] | .. ].
Ltac custom2 H0 :=  unfold H0; [auto | .. ].
Ltac custom3  :=  custom0 ; [auto | .. ].