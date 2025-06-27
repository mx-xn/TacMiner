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

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <= (count 0 s). 
Proof.
  intros. 
  induction s as [| x xs IH]. 
  - simpl. auto. 
Admitted. 
(** [] *)

End NatList. 