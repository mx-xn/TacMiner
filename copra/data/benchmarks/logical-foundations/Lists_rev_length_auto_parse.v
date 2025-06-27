(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Require Import Coq.Strings.String.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one (as with [nybble], and the following): *)

(** If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity and its
    built-in simplification: *)

(** **** Exercise: 1 star, standard (snd_fst_is_swap) *)

(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.


Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | cons h t => rev t ++ [h]
  end.

Lemma lem_1_1_1: rev [] = [].
Proof. intros. Admitted.

Lemma lem_1_1_2: length [] = 0.
Proof. intros. Admitted.

Lemma lem_1_1: length (rev []) = length [].
Proof. intros. Admitted.

Lemma lem_1_2_1: forall n l', rev (cons n l') = rev l' ++ [n].
Proof. intros. Admitted.

Lemma lem_1_2_2: forall L K : natlist, length (L ++ K) = length L + length K.
Proof. intros. Admitted.

Lemma lem_1_2: forall n l',
    length (rev l') = length l' ->
    length (rev (cons n l')) = length (cons n l').
Proof. intros. Admitted.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros. 
Admitted. 

End NatList.

(* 2025-01-13 16:00 *)
