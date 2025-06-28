Require Import List.
Require Import Arith.
Require Import Lia.

Fixpoint nth_option {A:Type}(n:nat)(l:list A)
  : option A :=
  match n, l with
  | O, cons a _ =>  Some a
  | S p, cons  _ tl => nth_option  p tl
  | _, nil => None
  end.

Lemma nth_length {A : Type} :
  forall (n:nat)(l:list A), nth_option  n l = None <->
                                   length l <= n.
Proof.
induction n as [ | p IHp ];
[destruct l as [ | l a ];
  [simpl; [split; [auto with arith |auto with arith]]
  |simpl; [split; [discriminate 1 |inversion 1]]]
  |intro l;
    [destruct l as [ | a l' ];
      [split; [auto with arith |auto with arith]
      |simpl; [rewrite ( IHp l' );
        [split; [auto with arith |auto with arith]]]]]].
Qed.
