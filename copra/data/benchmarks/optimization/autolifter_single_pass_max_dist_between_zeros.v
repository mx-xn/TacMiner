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
  | TrueB, _     => TrueB
  | _, TrueB     => TrueB
  | FalseB, FalseB => FalseB
  end.

(* A simple singly‐linked list of Bool *)
Inductive List : Type :=
| Nil
| Cons (h : Bool) (t : List).

(* tf0 rebuilds its argument *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => l
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil        => x
  | Cons h t   => Cons h (tf0 t)
  end.

(* A simple Peano natural number *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* lexicographic “less‐or‐equal” on Nat returning Bool *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero,    Succ _  => TrueB
  | _,       Zero    => FalseB
  | Succ n', Succ m' => lq n' m'
  end.

(* conditional for Nat results *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* maximum of two Nat *)
Definition max (n m : Nat) : Nat :=
  ite1 (lq n m) m n.

(* Compute the maximum distance between successive FalseB in a list of Bool.
   We carry an “accumulator” acc measuring the current run‐length of TrueB’s,
   and take the max over all runs once we hit the next FalseB. *)
Fixpoint tf4 (acc : Nat) (l : List) : Nat :=
  match l with
  | Nil => Zero
  | Cons h t =>
    let acc' := ite1 (negb h) Zero (plus acc (Succ Zero)) in
    max acc' (tf4 acc' t)
  end.

Definition tf3 (acc : Nat) (l : List) : Nat := tf4 acc l.

Definition maxdistbetweenzeros (l : List) : Nat := tf3 Zero l.

(* single‐pass definitions *)
Definition tf2 (l : List) : Nat := maxdistbetweenzeros (tf0 l).

Definition singlepass (l : List) : Nat := tf2 l.

Definition main (l : List) : Nat := singlepass l.

(* A 2‐tuple of Nat×Nat *)
Inductive Tuple2 : Type :=
| MakeTuple2 (fst : Nat) (snd : Nat).

Definition fst2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 x _ => x end.

Definition snd2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 _ y => y end.

(* Another way to compute the same max‐distance: return a pair
   (current‐run‐length, best‐so‐far) as we traverse the list *)
(* Alternative traversal building a Tuple2 *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil    => MakeTuple2 Zero Zero
  | Cons h t =>
      let p := tf5 t in
      let f := fst2 p in
      let s := snd2 p in
      let f' := if orb (negb h) (lq s f) then f else plus (Succ Zero) f in
      let s' := if negb h then Zero else plus (Succ Zero) s in
      MakeTuple2 f' s'
  end
  with tf5 (l : List) : Tuple2 :=
  match l with
  | Nil    => MakeTuple2 Zero Zero
  | Cons h t =>
      let p := tf6 t in
      let f := fst2 p in
      let s := snd2 p in
      let f' := if orb (negb h) (lq s f) then f else plus (Succ Zero) f in
      let s' := if negb h then Zero else plus (Succ Zero) s in
      MakeTuple2 f' s'
  end.

Definition tf7 (l : List) : Nat := fst2 (tf5 l).

Definition singlepassNew (l : List) : Nat := tf7 l.

Definition mainNew (l : List) : Nat := singlepassNew l.

(* Theorem stating that the two implementations coincide *)
Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.