(* Custom Boolean type *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* Peano‐style natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* Addition on Nat *)
Fixpoint plus (m n : Nat) : Nat :=
  match m with
  | Zero   => n
  | Succ p => Succ (plus p n)
  end.

(* Multiplication on Nat *)
Fixpoint times (m n : Nat) : Nat :=
  match m with
  | Zero   => Zero
  | Succ p => plus (times p n) n
  end.

(* A list of Nat *)
Inductive List : Type :=
| Nil  : List
| Cons : Nat -> List -> List.

(* A nested list type NList *)
Inductive NList : Type :=
| Single : List -> NList
| Ncons  : List -> NList -> NList.

Fixpoint product (l: List) : Nat :=
  match l with
  | Nil        => Zero
  | Cons x xs  => times x (product xs)
  end.

(* tf1 : NList -> List, tf0 = tf1 *)
(* tf1: NList -> List *)
Fixpoint tf1 (nl : NList) : List :=
  match nl with
  | Single l       => Cons (product l) Nil
  | Ncons l nl'    => Cons (product l) (tf0 nl')
  end
with tf0 (nl : NList) : List := 
  match nl with
  | Single l       => Cons (product l) Nil
  | Ncons l nl'    => Cons (product l) (tf1 nl')
  end.

(* tf0 is the same as tf1 *)

(* map = tf0 *)
Definition map (nl : NList) : List := tf0 nl.

(* Sum of a List of Nat *)
Fixpoint tf3 (l : List) : Nat :=
  match l with
  | Nil        => Zero
  | Cons x xs  => plus x (tf2 xs)
  end
with tf2 (l : List) : Nat :=  
  match l with
  | Nil        => Zero
  | Cons x xs  => plus x (tf3 xs)
  end.

(* tf2 is the same as tf3 *)
Definition sum := tf2.

(* Product of a List of Nat *)
Fixpoint tf5 (l : List) : Nat :=
  match l with
  | Nil        => Succ Zero
  | Cons x xs  => times x (tf4 xs)
  end
with tf4 (l : List) : Nat :=  
  match l with
  | Nil        => Succ Zero
  | Cons x xs  => times x (tf5 xs)
  end.

(* tf4 is the same as tf5 *)
Definition product2 := tf4. 

(* tails: List -> NList via tf6 and tf7 *)
Fixpoint tf7 (prefix xs : List) : NList :=
  match xs with
  | Nil        => Single prefix
  | Cons _ ys  => Ncons prefix (tf6 ys)
  end
with tf6 (l : List) : NList :=
  match l with
  | Nil        => Single l
  | Cons x xs  => Ncons l (tf7 xs xs)
  end. 

(* tf6 is the same as tf7 *)

Definition tails := tf6.

(* main = sum (map (tails l)) *)
Definition main (l : List) : Nat :=
  sum (map (tails l)).

(* A pair of Nat × Nat *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Nat -> Nat -> Tuple2.

Definition fst2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 x _ => x end.

Definition snd2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 _ y => y end.

(* New tails function computing Tuple2 *)
Fixpoint tf9 (l : List) : Tuple2 :=
  match l with
  | Nil       => MakeTuple2 (Succ Zero) (Succ Zero)
  | Cons x xs =>
    let p := tf8 xs in
    MakeTuple2
      (plus (fst2 p) (times x (snd2 p)))
      (times x (snd2 p))
  end
with tf8 (l : List) : Tuple2 :=
  match l with
  | Nil       => MakeTuple2 (Succ Zero) (Succ Zero)
  | Cons x xs =>
    let p := tf9 xs in
    MakeTuple2
      (plus (fst2 p) (times x (snd2 p)))
      (times x (snd2 p))
  end.
(* tf8 is the same as tf9 *)

Definition tailsNew := tf8.

(* mainNew = fst2 (tailsNew l) *)
Definition mainNew (l : List) : Nat :=
  fst2 (tailsNew l).

(* Theorem stating the optimization equivalence *)
Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.
