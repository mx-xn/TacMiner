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

(*  ├─ (1.1) [ Base Case: s = [] ; Definitions: remove_one 0 [] = [] and count 0 [] = 0 ] *)
Lemma remove_one_base:
  (count 0 (remove_one 0 [])) <= count 0 []. 
Proof.
  simpl. 
  unfold count. 
  unfold remove_one. 
  auto. 
Qed. 

Lemma remove_one_ind:
  forall (x : nat) (xs : bag),
  (count 0 (remove_one 0 xs)) <= count 0 xs ->
  (count 0 (remove_one 0 (cons x xs))) <= count 0 (cons x xs).
Proof.
  intros. 
  (* [ count 0 (remove_one 0 (cons x xs))) <= count 0 (cons x xs) ] *)
  simpl. 
  (* [ remove_one 0 (cons x xs) = if x =? 0 then xs else cons x (remove_one 0 xs) ] *)
  destruct (x =? 0) eqn:Heq. 
  - (* [ x =? 0 = true ] *)
    apply Nat.eqb_eq in Heq. 
    subst. 
    (* [ count 0 xs <= count 0 (cons x xs) ] *)
    auto. 
  - (* [ x =? 0 = false ] *)
    apply Nat.eqb_neq in Heq. 
    (* [ count 0 (remove_one 0 xs) <= count 0 (cons x xs) ] *)
    auto. 
Admitted. 

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <= (count 0 s). 
Proof.
  intros. 
  induction s as [| x xs IH]. 
  - simpl. auto. 
  - apply remove_one_ind. 
  auto. 
Admitted. 
(** [] *)

End NatList. 