Require Export Arith.
Require Export ArithRing.
Require Export Lia.
Require Export Recdef.
 
Fixpoint exp2 (n : nat) : nat :=
 match n with 0 => 1 | S p => 2 * exp2 p end.

(** An induction principle adapted to division by two *)

Theorem div2_rect:
 forall (P : nat ->  Type),
 P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall (n : nat),  P n.
Proof.
intros P X0 X1 Xrec n; assert (P n * P (S n))%type.
 - elim n; intuition.
 - intuition.
Defined.
 
Theorem div2_spec:
 forall n,  ({x : nat | 2 * x = n}) + ({x : nat | 2 * x + 1 = n}).
Proof. 
  intros n; induction  n  as [ | | n Hrec] using div2_rect.
  - left; now exists 0.
  - right; now exists 0.
  - destruct Hrec as  [[x Heq]|[x Heq]].
     + left; exists (S x); rewrite <- Heq; ring.
     + right; exists (S x); rewrite <- Heq; ring.
Qed.
 
Theorem half_smaller0: forall n x, 2 * x = S n ->  (x < S n).
Proof.
 intros; lia.
Qed.
 
Theorem half_smaller1: forall n x, 2 * x + 1 = n ->  (x < n).
Proof.
 intros; lia.
Qed.
 
Definition log2_F':
  forall (n : nat),
    (forall (y : nat),
        y < n -> y <> 0 ->  ({p : nat | exp2 p <= y /\ y < exp2 (p + 1)})) ->
    n <> 0 ->  ({p : nat | exp2 p <= n /\ n < exp2 (p + 1)}).
Proof. 
  intros n; case n.
  - intros log2 Hn0; elim Hn0; trivial.
  - intros n' log2. elim (div2_spec (S n')).
    + intros x. destruct x. case_eq x.
      * simpl; intros. subst; discriminate.
      * intros x' Heqx'; assert (Hn0: S x' <> 0) by auto with arith.
        subst x;  destruct (log2 (S x') (half_smaller0 _ _ e) Hn0) as [v Heqv].
        exists (S v); simpl;rewrite <- e;lia.
    + intros x. destruct x. destruct x; simpl.
      *  rewrite <- e.  exists 0; simpl; auto with arith.
      * rewrite <- e. 
        assert (Hn0: S x <> 0) by auto with arith.
        destruct (log2 (S x)) as [a Ha].
        -- lia.
        -- auto.
        -- exists (S a). simpl. lia.
Qed.

Section log2_function.

Lemma exp2_positive : forall n, exp2 n <> 0.
Proof. 
 induction n as [ | n IHn].
 - discriminate.  
 - simpl;  destruct (exp2 n).
   + now destruct IHn.   
   + discriminate.
Qed.


Fixpoint div2 (n:nat) : nat :=
match n with 0 | 1 => 0
            | S (S p) => S (div2 p)
end.

Lemma div2_double : forall n, div2 (2 * n) = n.
Proof.   
  induction n as [ | n IHn].
 -   simpl;auto.
 -  replace (2 * S n) with (S (S (2 * n))) by lia.
    simpl in *; now rewrite IHn.
Qed.

Theorem div2_rect' :
  forall (P : nat ->  Type),
    P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall (n : nat),  P n.
Proof.
  intros P H0 H1 Hrec n; assert (P n * P (S n))%type.
  - elim n; intuition.
  - intuition.
Qed.


Lemma div2_le : forall n,  div2 n <= n.
Proof.
  induction n using  div2_rect; auto.
  - simpl;auto with arith.
Qed.

Lemma div2_lt : forall n,  n <> 0 -> div2 n < n.
Proof.
  induction n as [| | n IHn] using div2_rect; auto.
  - now destruct 1.
  - simpl;intros.
    apply Nat.le_lt_trans with (S n);auto.
    generalize (div2_le n);auto with arith.
Qed.

Function log2 (n:nat) {measure (fun n:nat => n)} :=
match n with 0 | 1 => 0
           | _ => S (log2 (div2 n))
end.
Proof. 
 intros; apply div2_lt; discriminate.
Qed. 

(** Tests :

About log2_rect.
*)

Lemma log_of_exp2_0  : forall n p, n = exp2 p -> log2  n = p. 
Proof.
 intro n; functional induction (log2 n).
 - induction p;simpl; try discriminate.
   intro H; case_eq (exp2 p).
     intro H0;  destruct (exp2_positive p);auto.      
     intros n H0;rewrite H0 in H;discriminate.
 -  destruct p.
    + auto.
    + simpl.
      intro H.
      case_eq (exp2 p).
      * intro H0; destruct (exp2_positive p);auto.
      * intros n H0;  rewrite H0 in H.  exfalso; lia.   
 - intros p H;  destruct p. 
   +  simpl in H;  subst n; contradiction. 
   +  simpl in H; rewrite (IHn0 p); auto. 
    rewrite H;   generalize (div2_double (exp2 p));auto.
Qed.

Lemma log_of_exp2 : forall n:nat, log2 (exp2 n) = n.
Proof.
 intro n; now apply log_of_exp2_0.
Qed.
End log2_function. 

Section log2_it.
Theorem div2_ind:
 forall (P : nat ->  Prop),
 P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall n,  P n.
Proof.
intros P H0 H1 Hstep n.
assert (H : P n /\ P (S n)) by (elim n; intuition).
 now destruct H.
Qed.
 
Theorem div2_lt': forall n,  (div2 (S n) < S n).
Proof.
intros; elim n using div2_ind; simpl; intros; lia.
Qed.
 
Definition log2_it_F (log2 : nat ->  nat) (n : nat) : nat :=
   match n with
     0 => 0
    | 1 => 0
    | S (S p) => S (log2 (div2 (S (S p))))
   end.
 
Fixpoint iter {A : Type} (f : A ->  A) (k : nat) (a : A) {struct k} : A :=
 match k with   0%nat => a
               | S p => f (iter  f p a) end.

 
Definition log2_terminates:
 forall (n : nat),
  ({v : nat | exists p : nat , forall k g, p < k ->  iter log2_it_F k g n = v }).
Proof. 
 intros n; elim n  using (well_founded_induction lt_wf); clear n.
 intros n; case n.
 - intros; exists 0; exists 0; intros k; case k.
   + intros; lia.
   + intros k' g; simpl; auto.
 - intros n'; case n'.
   + intros; exists 0; exists 0; intros k; case k.
     * intros; lia.
     * intros k' g; simpl; auto.
   + intros p f; assert (Hlt: div2 (S (S p)) < S (S p)) by apply div2_lt'.
     destruct (f (div2 (S (S p))) Hlt) as [v Hex];exists (S v).
     destruct Hex as [p' Heq];exists (S p').
     intros k g; case k.
     * intros; lia.
     * intros k' Hltk;rewrite <- (Heq k' g); auto.
       lia.
Qed.
 
Definition log2' (n : nat) : nat :=
   match log2_terminates n with exist _ v _ => v end.
 
Theorem log2_fix_eqn:
 forall n, log2' n = match n with
                       0 => 0
                      | 1 => 0
                      | S (S p) => S (log2' (div2 (S (S p))))
                     end.
Proof. 
 intros n; unfold log2'; case (log2_terminates n); case n.
 - intros v [p Heq]; rewrite <- (Heq (S p) log2'); auto.
 - intros n'; case n'.
   + intros v [p Heq];rewrite <- (Heq (S p) log2'); auto.
   + intros n'' v [p Heq];case (log2_terminates (div2 (S (S n'')))).
     intros v' [p' Heq'];
     rewrite <- (Heq (S (S (p + p'))) log2'),
             <- (Heq' (S (p + p')) log2'); auto.
     lia.
     lia.
Qed.
 
Theorem div2_eq: forall n,  2 * div2 n = n \/ 2 * div2 n + 1 = n.
Proof.
intros n; elim n  using div2_ind; simpl; lia.
Qed.
 
Theorem log2_power:
 forall n, 0 < n ->  ( exp2 (log2' n) <= n < 2 * exp2 (log2' n) ).
Proof. 
intros n; elim n  using (well_founded_ind lt_wf).
intros x; case x.
- simpl; intros; lia.
- intros x'; case x'.
  + rewrite (log2_fix_eqn 1); simpl; auto with arith.
  + intros p Hrec; elim (Hrec (div2 (S (S p)))).
    * intros Hle Hlt _; rewrite (log2_fix_eqn (S (S p))).
      cbv zeta iota beta delta [exp2]; fold exp2.
      split.
      apply Nat.le_trans with (2 * div2 (S (S p))).
      auto with arith.
      elim (div2_eq (S (S p))).
      lia.
      lia.
      apply Nat.le_lt_trans with (2 * div2 (S (S p)) + 1).
      elim (div2_eq (S (S p))).
      lia.
      lia.
      lia.
    * apply div2_lt; simpl; auto with arith.
    * simpl; auto with arith.
Qed.
End log2_it.