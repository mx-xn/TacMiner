Require Export ZArith.
Require Import Relations.
Require Import Lia.

(** Example of use of the conversion rule
*)
Theorem conv_example : forall n:nat, 7*5 < n -> 6*6 <= n.
Proof.
 intros. assumption.
Qed.

Theorem imp_trans : forall P Q R:Prop, (P->Q)->(Q->R)->P->R.
Proof.
  intros P Q R H H0 p.
  apply H0. apply H. assumption.
Qed.

(** Tests :

Print imp_trans.

Check (imp_trans _ _ _ (le_S 0 1)(le_S 0 2)).

*)

Definition neutral_left (A:Type)(op:A->A->A)(e:A) : Prop :=
  forall x:A, op e x = x.

Lemma one_neutral_left : neutral_left Z Zmult 1%Z.
Proof.
 intro z; ring.
Qed.

Lemma le_i_SSi : forall i:nat, i <= S (S i).
Proof.
 intro i.
 do 2 apply le_S; apply le_n.
Qed.

Lemma all_imp_dist   :
 forall (A:Type)(P Q:A->Prop),
         (forall x:A, P x -> Q x)->
         (forall y:A, P y)->
          forall z:A, Q z.
Proof.
 intros A P Q H H0 z.
 apply H. apply H0.
Qed.


Lemma mult_le_compat_r : forall m n p:nat, le n p -> le (n * m) (p * m).
Proof.
 intros m n p H. rewrite (Nat.mul_comm n m).
   rewrite (Nat.mul_comm p m).
 apply Nat.mul_le_mono_l. assumption.
Qed.


Lemma le_mult_mult :
   forall a b c d:nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
 intros a b c d H H0.
 apply Nat.le_trans with (m := c * b).
 - apply mult_le_compat_r; assumption.
 - apply Nat.mul_le_mono_l; assumption.
Qed.


(** using eapply ...
*)

Lemma le_mult_mult' :
 forall a b c d:nat, a <= c -> b <= d -> a*b <= c*d.
Proof.
 intros a b c d H H0.
 eapply Nat.le_trans.
 - eapply Nat.mul_le_mono_l.
   eexact H0.
 -  apply mult_le_compat_r. assumption.
Qed.

Lemma le_O_mult : forall n p:nat, 0 * n <= 0 * p.
Proof.
 intros n p; apply le_n.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
 unfold lt; apply le_n.
Qed.

(** Tests :

SearchPattern (_ + _ <= _)%Z.

SearchPattern (?X1 * _ <= ?X1 * _)%Z.

*)

Lemma lt_S : forall n p:nat, n < p -> n < S p.
Proof.
 intros n p H.
 unfold lt; apply le_S. assumption.
Qed.

Open Scope Z_scope.

Definition Zsquare_diff (x y:Z):= x * x - y * y.

Theorem unfold_example :
 forall x y:Z,
   x*x = y*y ->
   Zsquare_diff x y * Zsquare_diff (x+y)(x*y) = 0.
Proof.
 intros x y Heq.
 unfold Zsquare_diff at 1.
 rewrite Heq; ring.
Qed.

Section ex_falso_quodlibet.
 Hypothesis ff : False.

 Lemma ex1 : 220 = 284.
 Proof.
   apply False_ind.
   exact ff.
 Qed.

End ex_falso_quodlibet.

Theorem absurd : forall P Q:Prop, P -> ~P -> Q.
Proof.
 intros P Q p H.
 elim H.
 assumption.
Qed.

Theorem double_neg_i : forall P:Prop, P->~~P.
Proof.
 intros P p H.
 apply H; assumption.
Qed.

Theorem modus_ponens :forall P Q:Prop, P->(P->Q)->Q.
Proof.
intros. auto.
Qed.


Theorem double_neg_i' : forall P:Prop, P -> ~ ~ P.
Proof.
 intro P; exact (modus_ponens P False).
Qed.

Theorem contrap :forall A B:Prop, (A->B) -> ~B -> ~A.
Proof.
 intros A B; unfold not.
 apply imp_trans.
Qed.

Theorem disj4_3' : forall P Q R S:Prop, R -> P \/ Q \/ R \/ S.
Proof.
  right; right; left; assumption.
Qed.

Lemma and_commutes : forall A B:Prop, A /\ B -> B /\ A.
Proof.
 intros A B H; destruct H.
 split; assumption.
Qed.

Lemma or_commutes : forall A B:Prop, A\/B->B\/A.
Proof.
 intros A B H; destruct H as [H | H]; auto.
Qed.

Lemma ex_imp_ex :
 forall (A:Type)(P Q:A->Prop), (ex P)->(forall x:A, P x -> Q x)->(ex Q).
Proof.
 intros A P Q H H0; destruct H as [a Ha].
 exists a; apply H0; assumption.
Qed.


Lemma diff_of_squares : forall a b:Z, ((a + b) * (a - b) = a * a - b * b)%Z.
Proof.
 intros; ring.
Qed.

Theorem eq_sym' : forall (A:Type)(a b:A), a = b -> b = a.
Proof.
 intros A a b e; rewrite e; reflexivity.
Qed.

Lemma Zmult_distr_1 : forall n x:Z, n * x + x = ( n + 1) * x.
Proof.
 intros n x ; rewrite Zmult_plus_distr_l.
 now rewrite  Zmult_1_l.
Qed.

Lemma regroup : forall x:Z, x + x + x + x + x = 5 * x.
Proof.
 intro x; pattern x at 1.
 rewrite <- Zmult_1_l.
 repeat rewrite Zmult_distr_1.
 reflexivity.
Qed.


Open Scope nat_scope.

Theorem le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
 intros; lia.
Qed.

Lemma conditional_rewrite_example : forall n:nat,
   8 <= n + 6 ->  3 + n < 6 -> n * n = n + n.
Proof.
 intros n H H0.
 rewrite <- (le_lt_S_eq 2 n).
 - reflexivity.
 -  apply  Nat.add_le_mono_l with (p := 6).
    rewrite Nat.add_comm in H; auto with arith.
 - apply Nat.add_lt_mono_l with (p:= 3); auto with arith.
Qed.

(** A shorter proof ...
*)

Lemma conditional_rewrite_example' : forall n:nat,
   8 <= n + 6 ->  3 + n < 6 -> n * n = n + n.
Proof.
 intros n H H0.
 assert (n = 2) by lia.
 now subst n.
Qed.


Theorem eq_trans :
   forall (A:Type)(x y z:A), x = y -> y = z -> x = z.
Proof.
 intros A x y z H. rewrite H; auto.
Qed.

Definition my_True : Prop
:= forall P:Prop, P -> P.

Definition my_False : Prop
:= forall P:Prop, P.

Theorem my_I : my_True.
Proof.
 intros P p; assumption.
Qed.


Theorem my_False_ind : forall P:Prop, my_False->P.
Proof.
 intros P F; apply F.
Qed.

Definition my_not (P:Prop) : Prop := P->my_False.

Section leibniz.

 Variable A : Type.

 Definition leibniz (a b:A) : Prop :=
 forall P:A -> Prop, P a -> P b.


Theorem leibniz_sym : symmetric A leibniz.
Proof.
 intros x y H Q; apply H; trivial.
Qed.

End leibniz.

Definition my_and (P Q:Prop) :=
  forall R:Prop, (P->Q->R)->R.

Definition my_or (P Q:Prop) :=
  forall R:Prop, (P->R)->(Q->R)->R.

Definition my_ex (A:Type)(P:A->Prop) :=
  forall R:Prop, (forall x:A, P x -> R)->R.

Definition my_le (n p:nat) :=
  forall P:nat -> Prop, P n ->(forall q:nat, P q -> P (S q))-> P p.

Section class.
Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Lemma excluded_middle_peirce : excluded_middle -> peirce.
Proof.
 unfold peirce. intros H P Q H0.
 destruct (H P) as [p | np].
 ** assumption.
 ** apply H0. intro H1. now absurd P.
Qed.

Lemma peirce_classic : peirce -> classic.
Proof.
 intros HPeirce P H0. apply (HPeirce P False).
 intro H1. now destruct H0.
Qed.

Lemma classic_excluded_middle: classic -> excluded_middle.
Proof.
 unfold excluded_middle. intros H P.
 apply H. intro H0. absurd P.
 - intro H1. apply H0. now left.
 - apply H. intro H1. apply H0. now right.
Qed.


Lemma excluded_middle_implies_to_or :  excluded_middle -> implies_to_or.
Proof.
 intros H P Q H0.
  destruct (H P) as [p | np].
  - right. auto.
  - now left.
Qed.

Lemma implies_to_or_excluded_middle : implies_to_or -> excluded_middle.
Proof.
 unfold excluded_middle. intros H P. destruct (H P P).
 - auto.
 - auto.
 - auto.
Qed.

Lemma classic_de_morgan_not_and_not : classic ->
                                      de_morgan_not_and_not.
Proof.
 unfold de_morgan_not_and_not. intros H P Q H0.
 apply H.
 intro H1. apply H0. split.
 - intro. apply H1. auto.
 - intro. apply H1. auto.
Qed.

Lemma de_morgan_not_and_not_excluded_middle : de_morgan_not_and_not ->
                                              excluded_middle.
Proof.
 unfold excluded_middle. intros H P.
 apply H. intros [H1 H2]. contradiction.
Qed.
End class.

Section my_le.
Theorem my_le_n : forall n:nat, my_le n n.
Proof.
 intros n P Hn HS ; assumption.
Qed.

Theorem my_le_S : forall n p:nat,
                  my_le n p -> my_le n (S p).
Proof.
 intros n p H P Hn HS.
 apply HS; apply H; assumption.
Qed.


Theorem my_le_le : forall n p:nat,
                    my_le n p -> n <= p.
Proof.
 intros n p H; apply H; auto with arith.
Qed.

Definition my_lt n p := my_le (S n) p.

Lemma my_lt_le : forall n p, my_lt n p -> my_le n p.
Proof.
 intros n p H;apply H.
 -  apply my_le_S;apply my_le_n.
 - intros;apply my_le_S;assumption.
Qed.

Theorem my_le_trans : forall n p q:nat, 
                        my_le n p -> my_le p q -> my_le n q.
Proof.
 intros n p q H;generalize q;clear q;apply H.
 - trivial.
 -intros q Hq r Hr;apply Hq; now apply my_lt_le.
Qed.
End my_le.

Section impred.
Theorem my_and_left : forall P Q:Prop, my_and P Q -> P.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_right : forall P Q:Prop, my_and P Q -> Q.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_ind : forall P Q R:Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
  intros P Q R H H0; apply H0; assumption.
Qed.

Theorem my_or_introl : forall P Q:Prop, P -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_intror : forall P Q:Prop, Q -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_ind : forall P Q R:Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
Proof.
  intros P Q R H H0 H1; apply H1; assumption.
Qed.

Theorem my_or_False : forall P:Prop, my_or P my_False -> P.
Proof.
 unfold my_False; intros P H; apply H; intro H0; apply H0.
Qed.

Theorem my_or_comm : forall P Q:Prop, my_or P Q -> my_or Q P.
Proof.
 intros P Q H; apply H; intros H0 R; auto.
Qed.

Theorem my_ex_intro : forall (A:Type) (P:A -> Prop) (a:A), P a -> my_ex A P.
Proof.
 intros A P a Ha R H; eapply H; eauto.
Qed.

Theorem my_not_ex_all :
 forall (A:Type) (P:A -> Prop), my_not (my_ex A P) -> forall a:A, my_not (P a).
Proof.
 intros A P H a H';
 apply H; eapply my_ex_intro; eauto.
Qed.

Theorem my_ex_ex : forall (A:Type) (P:A -> Prop), my_ex A P -> ex P.
Proof.
 intros A P H; apply H.
 intros x Hx; exists x; assumption.
Qed.

Theorem ex_my_ex : forall (A:Type) (P:A -> Prop), ex P -> my_ex _ P.
Proof.
 intros A P H; elim H; intros x Hx R.
 intros H0; eapply H0; eapply Hx.
Qed.
End impred.

Section impred_not.
Theorem not_False : my_not my_False.
Proof.
 intro H; assumption. 
Qed.


Theorem triple_neg : forall P:Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
 unfold my_not; auto.
Qed.

Theorem P3PQ : forall P Q:Prop, my_not (my_not (my_not P)) -> P -> Q.
Proof.
 intros P Q H p; apply (triple_neg _ H p).
Qed.

Theorem imp_absurd : forall P Q R:Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
 intros P Q R H H0 p; apply (H0 p); auto. 
Qed.
End impred_not. 