(* Coq code generated from the given Isabelle definitions *)

(* Boolean type and operations *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition andb (x y : Bool) : Bool :=
match x, y with
| FalseB, _      => FalseB
| _, FalseB      => FalseB
| TrueB, TrueB   => TrueB
end.

Definition orb (x y : Bool) : Bool :=
match x, y with
| TrueB, _       => TrueB
| _, TrueB       => TrueB
| FalseB, FalseB => FalseB
end.

Definition negb (b : Bool) : Bool :=
match b with
| TrueB  => FalseB
| FalseB => TrueB
end.

(* Unit type *)
(* List of Bool *)
Inductive List : Type :=
| Nil  : List
| Cons : Bool -> List -> List.

(* tf0: rebuilds its input list *)
Fixpoint tf0 (l : List) : List :=
match l with
| Nil      => l
| Cons h t   => Cons h (tf0 t)
end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
match l2 with
| Nil    => x
| Cons h t => Cons h (tf0 t)
end.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

(* addition and multiplication on our Nat *)
Fixpoint plus (n m : Nat) : Nat :=
match n with
| Zero    => m
| Succ n' => Succ (plus n' m)
end.

Fixpoint times (n m : Nat) : Nat :=
match n with
| Zero    => Zero
| Succ n' => plus (times n' m) m
end.

(* ite1 for Nat result *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
match b with
| TrueB  => x
| FalseB => y
end.

(* tf4: Bool -> Nat -> List -> Nat *)
Fixpoint tf4 (b : Bool) (acc : Nat) (l : List) : Nat :=
match l with
| Nil      => acc
| Cons h t   =>
let acc' := ite1 (andb (negb b) h)
(plus acc (Succ Zero))
acc in
tf4 h acc' t
end.

(* tf3 is just an alias for tf4 *)
Definition tf3 := tf4.

(* count occurrences via tf3 starting from False,0 *)
Definition cnt1s (l : List) : Nat := tf3 FalseB Zero l.

(* tf2, singlepass, main *)
Definition tf2 (l : List) : Nat := cnt1s (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* Tuple2 of Nat × Bool *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Nat -> Bool -> Tuple2.

Definition fst2 (t : Tuple2) : Nat :=
match t with MakeTuple2 x _ => x end.

Definition snd2 (t : Tuple2) : Bool :=
match t with MakeTuple2 _ y => y end.

(* tf6: List -> Tuple2 *)
Fixpoint tf6 (l : List) : Tuple2 :=
match l with
| Nil    => MakeTuple2 Zero FalseB
| Cons h t =>
let p := tf5 t in
let acc := fst2 p in
let flag := snd2 p in
let acc' :=
ite1 (orb (negb h) flag)
acc
(plus (Succ Zero) acc) in
MakeTuple2 acc' h
end
with tf5 (l : List) : Tuple2 :=
match l with
| Nil    => MakeTuple2 Zero FalseB
| Cons h t =>
let p := tf6 t in
let acc := fst2 p in
let flag := snd2 p in
let acc' :=
ite1 (orb (negb h) flag)
acc
(plus (Succ Zero) acc) in
MakeTuple2 acc' h
end. 

(* tf7, singlepassNew, mainNew *)
Definition tf7 (l : List) : Nat := fst2 (tf5 l).
Definition singlepassNew (l : List) : Nat := tf7 l.
Definition mainNew (l : List) : Nat := singlepassNew l.

(* Theorem stating the optimization equivalence *)
Theorem optimize : forall inp0 : List,
main inp0 = mainNew inp0.
Proof.
intros.
(* proof omitted *)
Admitted. 