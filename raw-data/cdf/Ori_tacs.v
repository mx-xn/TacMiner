From Coq Require Import ZArith Lia Bool String List.
Local Open Scope Z_scope.
Definition addr := Z.

Record heap : Type := {
  contents :> addr -> option Z;
  isfinite :  exists i, forall j, i <= j -> contents j = None
}.

Program Definition hempty : heap :=
  {| contents := fun l => None |}.
Next Obligation.
  exists 0; auto.
Qed.

Definition hdisjoint (h1 h2: heap) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Definition hdisj3 (h1 h2 h3: heap) :=
  hdisjoint h1 h2 /\ hdisjoint h1 h3 /\ hdisjoint h2 h3.

Program Definition hunion (h1 h2: heap) : heap :=
  {| contents := fun l => if h1 l then h1 l else h2 l |}.
Next Obligation.
  destruct (isfinite h1) as (i1 & fin1), (isfinite h2) as (i2 & fin2).
  exists (Z.max i1 i2); intros. rewrite fin1, fin2 by lia. auto.
Qed.

Lemma hdisjoint_sym:
  forall h1 h2, hdisjoint h1 h2 <-> hdisjoint h2 h1.
Proof.
  unfold hdisjoint; intros; split; intros H l; specialize (H l); tauto.
Qed.

Lemma hdisjoint_union_l:
  forall h1 h2 h3,
  hdisjoint (hunion h1 h2) h3 <-> hdisjoint h1 h3 /\ hdisjoint h2 h3.
Proof.
  unfold hdisjoint, hunion; cbn; intros. split.
- intros D. split.
  * intros l. destruct (D l); auto.
    + destruct (h1 l).
      ** auto.
      ** auto.
  * intros l. destruct (D l).
    + auto. destruct (h1 l); auto.
       discriminate.
    + auto.
- intros [D1 D2] l. destruct (D2 l).
  + destruct (h1 l) eqn:H1.
    * auto. destruct (D1 l).
      ++ auto. congruence.
      ++ auto.
    * auto.
  + auto.
Qed.

Lemma hdisjoint_union_r:
  forall h1 h2 h3,
  hdisjoint h1 (hunion h2 h3) <-> hdisjoint h1 h2 /\ hdisjoint h1 h3.
Proof.
  intros. rewrite hdisjoint_sym. rewrite hdisjoint_union_l.
  rewrite (hdisjoint_sym h2), (hdisjoint_sym h3). tauto.
Qed.


Ltac HDISJ :=
  match goal with
  | [ H: hdisj3 _ _ _ |- _ ] =>
      destruct H as (? & ? & ?); HDISJ
  | [ H: hdisjoint (hunion _ _) _ |- _ ] =>
      apply hdisjoint_union_l in H; destruct H; HDISJ
  | [ H: hdisjoint _ (hunion _ _) |- _ ] =>
      apply hdisjoint_union_r in H; destruct H; HDISJ
  | [ |- hdisj3 _ _ _ ] =>
      split; [|split]; HDISJ
  | [ |- hdisjoint (hunion _ _) _ ] =>
      apply hdisjoint_union_l; split; HDISJ
  | [ |- hdisjoint _ (hunion _ _) ] =>
      apply hdisjoint_union_r; split; HDISJ
  | [ |- hdisjoint hempty _ ] =>
      red; auto
  | [ |- hdisjoint _ hempty ] =>
      red; auto
  | [ |- hdisjoint _ _ ] =>
      assumption || (apply hdisjoint_sym; assumption) || idtac
  | _ => idtac
  end.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation between states *)
Definition infseq (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

Lemma infseq_inv:
  forall a, infseq a -> exists b, R a b /\ infseq b.
Proof.
  intros a (X & Xa & XP). destruct (XP a Xa) as (b & Rab & Xb).
  exists b; split; auto. exists X; auto.
Qed.