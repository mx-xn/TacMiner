(* Coq code generated from the given Isabelle definitions *)

(* Boolean type and basic operations *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition negb (b : Bool) : Bool :=
  match b with
  | TrueB  => FalseB
  | FalseB => TrueB
  end.

Definition orb (x y : Bool) : Bool :=
  match x, y with
  | TrueB, _       => TrueB
  | _, TrueB       => TrueB
  | FalseB, FalseB => FalseB
  end.

Definition andb (x y : Bool) : Bool :=
  match x, y with
  | TrueB, TrueB   => TrueB
  | _, _           => FalseB
  end.

(* Unit type (not really used) *)
Inductive Unit : Type := Null.

(* Lists of Bool *)
Inductive List : Type :=
| Nil  : List
| Cons : Bool -> List -> List.

(* tf0: rebuild the list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => l
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1 x l = x if l = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil      => x
  | Cons h t => Cons h (tf0 t)
  end.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

(* less-or-equal lq : Nat → Nat → Bool *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero, Succ _     => TrueB
  | Zero, Zero       => TrueB       (* we include Zero ≤ Zero *)
  | Succ _, Zero     => FalseB
  | Succ n', Succ m' => lq n' m'
  end.

(* Conditional returning a Nat *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* max on Nat *)
Definition max (n m : Nat) : Nat :=
  ite1 (lq n m) m n.

(* addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

Fixpoint tf3 (a b : Nat) (l : List) : Nat :=
  match l with
  | Nil => max a b
  | Cons z zs =>
      (* compute new accumulator *)
      let next_acc :=
        (* if ¬ z then tf3 (max b a) Zero zs else tf3 b (a + 1) zs *)
        if negb z
        then tf3 (max a b) Zero zs
        else tf3 a (plus b (Succ Zero)) zs
        in next_acc
  end.  

(* tf4: Nat → Nat → List → Nat *)
Definition tf4 (x y : Nat) (l : List) : Nat :=
  match l with
  | Nil =>
      (* tf4 x y Nil = max y x *)
      max y x
  | Cons z zs =>
      (* compute new accumulator *)
      let next_acc :=
        (* if ¬ z then tf3 (max y x) Zero zs else tf3 y (x + 1) zs *)
        if negb z
        then tf3 (max y x) Zero zs
        else tf3 y (plus x (Succ Zero)) zs
      in
      next_acc
  end. 
(* tf3 swaps the first two Nat-arguments *)

(* max1s: count of 'max 1s' across the list after tf0 *)
Definition max1s (l : List) : Nat := tf3 Zero Zero l.

(* tf2, singlepass, main *)
Definition tf2 (l : List) : Nat := max1s (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* Tuple2 of Nat × Nat *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Nat -> Nat -> Tuple2.

Definition fst2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 x _ => x end.

Definition snd2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 _ y => y end.

(* tf6: List → Tuple2 *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil =>
      (* empty list → (0,0) *)
      MakeTuple2 Zero Zero
  | Cons z zs =>
      let p := tf6 zs in
      let f := orb (negb z)
                     (lq (snd2 p) (fst2 p)) in
      let first' :=
        (* if f then fst2 p else 1 + fst2 p *)
        if f then fst2 p else plus (Succ Zero) (fst2 p) in
      let second' :=
        (* if ¬ z then 0 else 1 + snd2 p *)
        if negb z then Zero else plus (Succ Zero) (snd2 p) in
      MakeTuple2 first' second'
  end.

Definition tf5 := tf6.

Definition tf7 (l : List) : Nat := fst2 (tf5 l).

Definition singlepassNew (l : List) : Nat := tf7 l.
Definition mainNew (l : List) : Nat := singlepassNew l.

(* Theorem: optimized version agrees with the original *)
Theorem optimize :
  forall inp0 : List,
    main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted. 