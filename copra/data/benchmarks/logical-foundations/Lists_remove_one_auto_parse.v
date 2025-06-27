(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Module NatList.


Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition bag := natlist. 

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | cons x xs => if x =? v then S (count v xs) else count v xs
  end. 

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | cons x xs => if x =? v then xs else cons x (remove_one v xs)
  end.

Lemma lem_1_1_1 : remove_one 0 [] = [].
Proof. intros. Admitted.

(* 1.1.2 *)
Lemma lem_1_1_2 : count 0 [] = 0.
Proof. intros. Admitted.

(* 1.1.3 *)
Lemma lem_1_1_3 : (0 <=? 0) = true.
Proof. intros. Admitted.

(* 1.1 *)
Lemma lem_1_1 : count 0 (remove_one 0 []) <=? count 0 [] = true.
Proof. intros. Admitted.

(* 1.2.1 *)
Lemma lem_1_2_1 : forall xs,
  count 0 (remove_one 0 (cons 0 xs)) <=? count 0 (cons 0 xs) = true.
Proof. intros. Admitted.

(* 1.2.2 *)
Lemma lem_1_2_2 : forall x xs,
  x <> 0 ->
  count 0 (remove_one 0 (cons x xs)) <=? count 0 (cons x xs) = true.
Proof. intros. Admitted.

(* 1.2 *)
Lemma lem_1_2 : forall x xs,
  count 0 (remove_one 0 xs) <=? count 0 xs = true ->
  count 0 (remove_one 0 (cons x xs)) <=? count 0 (cons x xs) = true.
Proof. intros. Admitted.

(* Main theorem *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <= (count 0 s). 
Proof.
  intros. 
  induction s as [| x xs IH]. 
  - simpl. auto. 
Admitted. 
(** [] *)

End NatList. 