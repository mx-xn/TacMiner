(* ********** Imports and Scope ********** *)
Require Import Coq.Init.Nat.
Open Scope nat_scope.

(* ********** Boolean type and operations ********** *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition andb (x y : Bool) : Bool :=
  match x, y with
  | TrueB, TrueB   => TrueB
  | _, _           => FalseB
  end.

Definition orb (x y : Bool) : Bool :=
  match x, y with
  | FalseB, FalseB => FalseB
  | _, _           => TrueB
  end.

Definition negb (b : Bool) : Bool :=
  match b with
  | TrueB  => FalseB
  | FalseB => TrueB
  end.

(* ite1 for selecting between two natural numbers *)
Definition ite1 (b : Bool) (x y : nat) : nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* ********** Lists of Bool ********** *)
Inductive List : Type :=
| Nil  : List
| Cons : Bool -> List -> List.

(* tf0: rebuild the list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => Nil
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil      => x
  | Cons h t => Cons h (tf0 t)
  end.

(* ********** A counter over lists: count10p ********** *)
(* tf4 carries two Bool-flags (b, acc) and the list, returns nat *)
Fixpoint tf4 (b acc : Bool) (l : List) : nat :=
  match l with
  | Nil       => 0
  | Cons h t  =>
    let add1 := if andb acc h then 1 else 0 in
    add1 + tf4 h (andb (negb h) (orb b acc)) t
  end.

(* tf3 is just tf4 *)
Definition tf3 := tf4.

(* count10p = tf3 False False *)
Definition count10p (l : List) : nat :=
  tf3 FalseB FalseB l.

(* tf2, singlepass, main *)
Definition tf2 (l : List) : nat := count10p (tf0 l).
Definition singlepass (l : List) : nat := tf2 l.
Definition main (l : List) : nat := singlepass l.

(* ********** A simple head-test ********** *)
Definition tf5 (l : List) : Bool :=
  match l with
  | Nil      => FalseB
  | Cons h _ => h
  end.

Definition alhead (l : List) : Bool := tf5 l.

(* ********** Tuple2 and helpers ********** *)
Inductive Tuple2 : Type :=
| MakeTuple2 : nat -> nat -> Tuple2.

Definition fst2 (t : Tuple2) : nat :=
  match t with MakeTuple2 x _ => x end.

Definition snd2 (t : Tuple2) : nat :=
  match t with MakeTuple2 _ y => y end.

(* nateq: test equality of two nats, returning our Bool *)
Definition nateq (n m : nat) : Bool :=
  if Nat.eqb n m then TrueB else FalseB.

(* ********** New counter collecting two pieces ********** *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil =>
    MakeTuple2 0 0
  | Cons h t =>
    let p := tf6 t in
    (* first component: bump if cond else leave *)
    let cond :=
      orb
        (orb (negb h)
             (nateq (fst2 p) (snd2 p)))
        (tf5 t) in
    let f1 := if cond then fst2 p else S (fst2 p) in
    (* second component: bump if h else leave *)
    let s1 := if negb h then snd2 p else S (snd2 p) in
    MakeTuple2 f1 s1
  end.

(* tf8 picks out the first component *)
Definition tf8 (l : List) : nat := fst2 (tf6 l).

Definition singlepassNew (l : List) : nat := tf8 l.
Definition mainNew      (l : List) : nat := singlepassNew l.

(* ********** Optimization theorem ********** *)
Theorem optimize : forall inp0 : List,
    main inp0 = mainNew inp0.
Proof.
  intros inp0.
  (* proof omitted *)
Admitted.