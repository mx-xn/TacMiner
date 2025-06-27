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


(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This seems natural, because the truth of
    the goal clearly doesn't depend on the list having been reversed.
    Moreover, it is easier to prove the more general property. *)

(** Now we can complete the original proof. *)

(* ├─ (1.1) [ l = []; Definitions: rev [] = []; length [] = 0 ]
    |- length (rev []) = length [] *)
Lemma rev_length_base: 
  length (rev []) = length []. 
Proof.
  simpl. 
  reflexivity. 
Admitted.

(*    ├─ (1.2.2) [ Lemma on list concatenation and definition of length [n] ]
   │  |- length (rev l' ++ [n]) = length (rev l') + length ([n]) = length (rev l') + 1 *)
(* Lemma rev_length_ind_2:
  forall l' : natlist, forall n : nat,
  length (rev l' ++ [n]) = length (rev l') + length ([n]) ->
  length (rev l' ++ [n]) = length (rev l') + 1 ->
  length (rev l' ++ [n]) = length (rev l') + 1. 
Proof. 
  intros l' n H1 H2. 
  rewrite H1. 
Admitted.  *)

(*    └─ (1.2.3) [ Inductive Hypothesis and Definition of length for cons lists: length (n :: l') = length l' + 1; also, length (rev l') = length l' ]
     |- length (rev l') + 1 = length (n :: l') *)
(* Lemma rev_length_ind_3:
  forall l' : natlist, forall n : nat,
  length (rev l') = length l' ->
  length (rev l') + 1 = length (cons n l'). 
Proof. 
  intros l' n H. 
  simpl. 
  rewrite H. 
Admitted.  *)

(* Lemma: ∀ L, K, length (L ++ K) = length L + length K *)
Lemma app_length:
  forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. 
  induction l1 as [| n l' IH]. 
  - simpl. auto. 
  - simpl. rewrite IH. auto. 
Qed. 

(* [ l = n :: l'; Inductive Hypothesis: length (rev l') = length l'; Definitions: rev (n :: l') = rev l' ++ [n], length [n] = 1; Lemma: ∀ L, K, length (L ++ K) = length L + length K ]
  |- length (rev (n :: l')) = length (n :: l') *)
Lemma rev_length_inductive:
  forall l : natlist, forall n : nat,
  length (rev l) = length l ->
  length (rev (cons n l)) = length (cons n l). 
Proof.
  intros l n IH. 
  simpl. 
Admitted. 

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros. 
  induction l as [| n l' IH]. 
  - apply rev_length_base. 
  - apply rev_length_inductive. 
    auto. 
Admitted. 

End NatList.

(* 2025-01-13 16:00 *)
