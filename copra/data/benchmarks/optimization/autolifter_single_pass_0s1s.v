(* Coq code generated from the given Isabelle definitions *)

(* Boolean type and operations *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition negb (b : Bool) : Bool :=
match b with
| TrueB  => FalseB
| FalseB => TrueB
end.

Definition andb (b1 b2 : Bool) : Bool :=
match b1, b2 with
| FalseB, _      => FalseB
| _, FalseB      => FalseB
| TrueB, TrueB   => TrueB
end.

Definition orb (b1 b2 : Bool) : Bool :=
match b1, b2 with
| TrueB, _       => TrueB
| _, TrueB       => TrueB
| FalseB, FalseB => FalseB
end.

Definition ite1 (b x : Bool) : Bool :=
match b with
| TrueB  => x
| FalseB => FalseB
end.

(* List type *)
Inductive List : Type :=
| Nil  : List
| Cons : Bool -> List -> List.

(* tf0 and tf1 without mutual recursion *)
Fixpoint tf0 (l : List) : List :=
match l with
| Nil      => l
| Cons h t   => Cons h (tf0 t)
end.

Definition tf1 (x l2 : List) : List :=
match l2 with
| Nil      => x
| Cons h t   => Cons h (tf0 t)
end.

(* zsos, tf2, singlepass, main *)
Fixpoint tf3 (b : Bool) (l : List) : Bool :=
match l with
| Nil      => TrueB
| Cons h t   => ite1 (orb (negb h) (andb b h)) (tf3 (andb b h) t)
end.

Definition zsos (l : List) : Bool := tf3 TrueB l.

Definition tf2 (l : List) : Bool := zsos (tf0 l).

Definition singlepass (l : List) : Bool := tf2 l.

Definition main (l : List) : Bool := singlepass l.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

Fixpoint nateq (n m : Nat) : Bool :=
match n, m with
| Zero,    Zero    => TrueB
| Zero,    Succ _  => FalseB
| Succ _,  Zero    => FalseB
| Succ n', Succ m' => nateq n' m'
end.

Fixpoint plus (n m : Nat) : Nat :=
match n with
| Zero    => m
| Succ n' => Succ (plus n' m)
end.

Definition ite3 (b : Bool) (x y : Nat) : Nat :=
match b with
| TrueB  => x
| FalseB => y
end.

(* Tuple2 and projections *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Bool -> Nat -> Tuple2.

Definition fst2 (t : Tuple2) : Bool :=
match t with
| MakeTuple2 x _ => x
end.

Definition snd2 (t : Tuple2) : Nat :=
match t with
| MakeTuple2 _ y => y
end.

(* tf6, tf7, singlepassNew, mainNew *)
Fixpoint tf6 (l : List) : Tuple2 :=
match l with
| Nil      => MakeTuple2 TrueB Zero
| Cons h t   =>
let p := tf6 t in
MakeTuple2
(orb (andb h (fst2 p)) (nateq (snd2 p) Zero))
(ite3 (negb h) (snd2 p) (plus (Succ Zero) (snd2 p)))
end.

Definition tf7 (l : List) : Bool := fst2 (tf6 l).

Definition singlepassNew (l : List) : Bool := tf7 l.

Definition mainNew (l : List) : Bool := singlepassNew l.

(* Theorem stating the optimization equivalence *)
Theorem optimize : forall inp0 : List, main inp0 = mainNew inp0.
Proof.
intros.
(** proof omitted *)
Admitted. 