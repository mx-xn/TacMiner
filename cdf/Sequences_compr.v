Set Implicit Arguments.

Section SEQUENCES.

From CDF Require Import Ori_tacs.

Variable A: Type.

Variable R: A -> A -> Prop.

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Ltac custom_tac6 H0 H1 := exists H0; split; auto; exists H1; auto.

Ltac custom_tac8 H0 H1 := intros; destruct ( @infseq_inv H0) as ( c & Rbc & _); eapply H1; eauto.

Ltac custom_tac7  := induction 1; intros; auto.

Ltac custom_tac2  := split; auto.

Ltac custom_tac0 H0 := intros; inversion H0.

Ltac custom_tac3 H0 := exists H0; auto.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof. induction 1; eauto using star. Qed.

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof. intros. inversion H. eauto using star. Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof. intros. inversion H. eauto using plus, star_trans. Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof. intros. inversion H0. inversion H; eauto using plus, star, star_trans. Qed.

Definition irred (a: A) : Prop := forall b, ~(R a b).

Inductive starN: nat -> A -> A -> Prop :=
  | starN_refl: forall a,
      starN O a a
  | starN_step: forall n a b c,
      R a b -> starN n b c -> starN (S n) a c.

Lemma starN_star:
  forall n a b, starN n a b -> star a b.
Proof. induction 1; econstructor; eauto. Qed.

Lemma star_starN:
  forall a b, star a b -> exists n, starN n a b.
Proof. induction 1. - exists O; constructor. - destruct IHstar as (n & Sn). exists (S n); econstructor; eauto. Qed.

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).

Definition infseq (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof. intros. exists (fun b => b = a); split. auto. intros. subst a1. exists a; auto. Qed.

Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof. intros a0 ALL0. exists all_seq_inf; split; auto. intros a1 ALL1. destruct (ALL1 a1) as [a2 R12]. constructor. exists a2; split; auto. intros a3 S23. destruct (ALL1 a3) as [a4 R23]. apply star_step with a2; auto. exists a4; auto. Qed.

Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof. intros a0 (f & F0 & Fn). exists (fun a => exists i, f i = a); split. - exists 0; auto. - intros a1 (i1 & F1). subst a1. exists (f (1 + i1)); split; auto. exists (1 + i1); auto. Qed.

Lemma infseq_inv:
  forall a, infseq a -> exists b, R a b /\ infseq b.
Proof. intros a (X & Xa & XP). destruct (XP a Xa) as (b & Rab & Xb). exists b; split; auto. exists X; auto. Qed.

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof. intros X H a0 Xa0. exists (fun a => exists b, star a b /\ X b); split. - exists a0; auto using star_refl. - intros a1 (a2 & S12 & X2). inversion S12. subst a. + destruct (H a2 X2) as (a3 & P23 & X3). inversion P23. subst a c. exists b; split; auto. exists a3; auto. + exists b; split; auto. exists a2; auto. Qed.

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof. induction 1; intros. - auto. - inversion H1. + subst a0 a. right. eauto using star. + subst a0 c1. assert (b = b0) by (eapply R_functional; eauto). subst b0. apply IHstar; auto. Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof. intros. destruct (star_star_inv H H1). - inversion H3. subst a0. auto. elim (H0 _ H4). - inversion H3. subst a0. auto. elim (H2 _ H4). Qed.

Lemma infseq_inv':
  forall a b, R a b -> infseq a -> infseq b.
Proof. intros a b Rab Ia. destruct (infseq_inv Ia) as (b' & Rab' & Xb'). assert (b' = b) by (eapply R_functional; eauto). subst b'. auto. Qed.

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof. induction 1; intros. - auto. - apply IHstar. apply infseq_inv' with a; auto. Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof. intros. destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto. apply (H0 c); auto. Qed.

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a. Proof. intros. unfold all_seq_inf. intros. destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto. exists c; auto. Qed.

End SEQUENCES.

