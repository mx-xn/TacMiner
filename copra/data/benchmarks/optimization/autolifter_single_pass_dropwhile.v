(* Boolean type and operations *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition negb (b : Bool) : Bool :=
  match b with
  | TrueB  => FalseB
  | FalseB => TrueB
  end.

(* List of Bool (omit the Unit parameter) *)
Inductive List : Type :=
| Nil
| Cons : Bool -> List -> List.

(* tf0: rebuilds the list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => l
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil      => x
  | Cons h t => Cons h (tf0 t)
  end.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

(* plus on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* ite1 for Nat result *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* tf4 : Nat -> List -> Nat *)
Fixpoint tf4 (acc : Nat) (l : List) : Nat :=
  match l with
  | Nil        => acc
  | Cons h t   =>
      (* if h then acc else tf4 (plus (Succ Zero) acc) t *)
      ite1 h acc (tf4 (plus (Succ Zero) acc) t)
  end.

(* tf3 is alias for tf4 *)
Definition tf3 := tf4.

(* dropwhile = tf3 Zero *)
Definition dropwhile (l : List) : Nat := tf3 Zero l.

(* tf2, singlepass, main *)
Definition tf2 (l : List) : Nat := dropwhile (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* tf6: alternative one-pass count *)
Fixpoint tf6 (l : List) : Nat :=
  match l with
  | Nil      => Zero
  | Cons h t =>
      (* if not h then Succ Zero + tf5 t else Zero *)
      ite1 (negb h) (plus (Succ Zero) (tf5 t)) Zero
  end
with tf5 (l : List) : Nat := 
  match l with
  | Nil      => Zero
  | Cons h t =>
      (* if not h then Succ Zero + tf5 t else Zero *)
      ite1 (negb h) (plus (Succ Zero) (tf6 t)) Zero
  end. 

(* tf7, singlepassNew, mainNew *)
Definition tf7 (l : List) : Nat := tf5 l.
Definition singlepassNew (l : List) : Nat := tf7 l.
Definition mainNew (l : List) : Nat := singlepassNew l.

(* Theorem stating the optimization equivalence *)
Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted. 