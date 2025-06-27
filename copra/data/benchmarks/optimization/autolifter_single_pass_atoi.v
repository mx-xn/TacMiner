(* Coq code generated from the given Isabelle definitions *)


(* Boolean type (unused in this fragment, but included for completeness) *)
Inductive Bool : Type := TrueB | FalseB.

Open Scope nat_scope.

(* Boolean operations *)
(* Natural numbers *)
(* Inductive Nat : Type :=
| Zero
| Succ (n : Nat). *)

(* A convenience constant for ten = Succ^10 Zero *)
Definition ten : nat := 10. 

(* Unit type *)
(* Inductive Unit : Type := Null. *)

(* List of Nats *)
Inductive List : Type :=
| Nil  
| Cons (h : nat) (t : List). 

(* tf0: rebuilds the list (identity up to reconstruction) *)
Fixpoint tf0 (l : List) : List :=
match l with
| Nil        => l
| Cons h t   => Cons h (tf0 t)
end.

(* tf1: returns [x] on an empty list, otherwise rebuilds like tf0 *)

(* tf1 x l2 = x if l2 = Nil, otherwise Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
match l2 with
| Nil   => x
| Cons h t => Cons h (tf0 t)
end.

(* tf3, tf4, atoi: compute a numeric code by recursing on the list *)
(* Assume the following declarations are in scope:
     Inductive List : Type := Nil : List | Cons : nat -> List -> List.
     Definition ten := ….
     Fixpoint plus ….
     Fixpoint times ….
*)

Fixpoint tf4 (l : List) : nat :=
  match l with
  | Nil        => 0
  | Cons h t   => (ten * tf4 t) + h
  end.

Definition tf3 (l : List) : nat := tf4 l.

(* atoi = tf3 *)
Definition atoi := tf3.

(* tf2 and singlepass = atoi ∘ tf0 *)
Definition tf2 (l : List) : nat := atoi (tf0 l).
Definition singlepass (l : List) : nat := tf2 l.
Definition main (l : List) : nat := singlepass l.

(* addition and multiplication on Nat *)
Definition plus (n m : nat) : nat :=
match n with
| 0    => m
| S n' => S (n' + m)
end.

Definition times (n m : nat) : nat :=
match n with
| 0    => 0
| S n' => (n' * m) + m
end.

(* tf6, tf5, tf7: an alternative traversal *)
(* Single recursive definition of tf6 *)

Fixpoint tf6 (l : List) : nat :=
match l with
| Nil    => 0 
| Cons h t => plus h (times (tf5 t) ten)
end
with tf5 (l : List) : nat := 
match l with 
| Nil => 0
| Cons h t => plus h (times (tf6 t) ten)
end. 

Definition tf7 (l : List) : nat := tf5 l. 
Definition singlepassNew (l : List) : nat := tf7 l.
Definition mainNew (l : List) : nat := singlepassNew l.

(* Theorem stating the optimization equivalence *)
Theorem optimize : forall inp0 : List,
main inp0 = mainNew inp0.
Proof.
intros.
(** proof omitted *)
Admitted. 