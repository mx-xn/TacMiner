Require Import Coqlib.

Require Errors.

Require Import Maps.

Require Import AST.

Require Import Integers.

Require Import Switch.

Require Import Op.

Require Import Registers.

Require Import CminorSel.

Require Import RTL.

Require Import RTLgen.


                                Remark bind_inversion1:
                                  forall (A B: Type) (f: mon A) (g: A -> mon B)
                                         (y: B) (s1 s3: state) (i: state_incr s1 s3),
                                  bind f g s1 = OK y s3 i ->
                                  exists x, exists s2, exists i1, exists i2,
                                  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
                                Proof.
                                  intros until i. unfold bind. destruct (f s1); intros.
                                  discriminate.
                                  exists a; exists s'; exists s.
                                  destruct (g a s'); inv H.
                                  exists s0; auto.
                                Qed.

                                Remark bind2_inversion1:
                                  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
                                         (z: C) (s1 s3: state) (i: state_incr s1 s3),
                                  bind2 f g s1 = OK z s3 i ->
                                  exists x, exists y, exists s2, exists i1, exists i2,
                                  f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
                                Proof.
                                  unfold bind2; intros.
                                  exploit bind_inversion1; eauto.
                                  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
                                  exists x; exists y; exists s2; exists i1; exists i2; auto.
                                Qed.

                                Ltac monadInv1 H :=
                                  match type of H with
                                  | (OK _ _ _ = OK _ _ _) =>
                                      inversion H; clear H; try subst
                                  | (Error _ _ = OK _ _ _) =>
                                      discriminate
                                  | (ret _ _ = OK _ _ _) =>
                                      inversion H; clear H; try subst
                                  | (error _ _ = OK _ _ _) =>
                                      discriminate
                                  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
                                      let x := fresh "x" in (
                                      let s := fresh "s" in (
                                      let i1 := fresh "INCR" in (
                                      let i2 := fresh "INCR" in (
                                      let EQ1 := fresh "EQ" in (
                                      let EQ2 := fresh "EQ" in (
                                      destruct (bind_inversion1 _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
                                      clear H;
                                      try (monadInv1 EQ2)))))))
                                  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
                                      let x1 := fresh "x" in (
                                      let x2 := fresh "x" in (
                                      let s := fresh "s" in (
                                      let i1 := fresh "INCR" in (
                                      let i2 := fresh "INCR" in (
                                      let EQ1 := fresh "EQ" in (
                                      let EQ2 := fresh "EQ" in (
                                      destruct (bind2_inversion1 _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
                                      clear H;
                                      try (monadInv1 EQ2))))))))
                                  end.

                                Ltac monadInv H :=
                                  match type of H with
                                  | (ret _ _ = OK _ _ _) => monadInv1 H
                                  | (error _ _ = OK _ _ _) => monadInv1 H
                                  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
                                  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
                                  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ _ _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  | (?F _ = OK _ _ _) =>
                                      ((progress simpl in H) || unfold F in H); monadInv1 H
                                  end.
                                

