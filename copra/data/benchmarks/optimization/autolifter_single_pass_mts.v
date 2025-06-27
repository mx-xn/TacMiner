(* Booleans *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* A list of natural numbers *)
Inductive List : Type :=
| Nil
| Cons (hd : Nat) (tl : List).

(* tf0: rebuild the list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => l
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1: if the list is empty, return x; otherwise rebuild the list tail *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil        => x
  | Cons h t   => Cons h (tf0 t)
  end.

(* lq n m = TrueB when n < m (as in the given equations), FalseB otherwise *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero,    Succ _  => TrueB
  | Succ n', Succ m' => lq n' m'
  | _, _             => FalseB
  end.

(* ite1: if b = TrueB then x else y *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* max n m = if lq n m then m else n *)
Definition max (n m : Nat) : Nat :=
  ite1 (lq n m) m n.

(* plus on our Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* A pair of Nats *)
Inductive Tuple2 : Type :=
| MakeTuple2 (fst snd : Nat).

(* projections *)
Definition fst2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 x _ => x end.
Definition snd2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 _ y => y end.

(* tf4: compute a pair (first,second) over the list *)
Fixpoint tf4 (l : List) : Tuple2 :=
  match l with
  | Nil => MakeTuple2 Zero Zero
  | Cons h t =>
    let p := tf4 t in
    let s := snd2 p in
    let f := fst2 p in
    MakeTuple2
      (max (plus s h) f)
      (plus s h)
  end.

(* alias tf3 = tf4 *)
Definition tf3 := tf4.

(* mts = first component of tf3 *)
Definition mts (l : List) : Nat :=
  fst2 (tf3 l).

(* tf2, singlepass, main *)
Definition tf2 (l : List) : Nat := mts (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* tf6: alternative pair computation *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil => MakeTuple2 Zero Zero
  | Cons h t =>
    let p := tf5 t in
    let f := fst2 p in
    let s := snd2 p in
    MakeTuple2
      (ite1 (lq (plus h s) f) f (plus h s))
      (plus h s)
  end
  with tf5 (l : List) : Tuple2 :=
  match l with
  | Nil => MakeTuple2 Zero Zero
  | Cons h t =>
    let p := tf6 t in
    let f := fst2 p in
    let s := snd2 p in
    MakeTuple2
      (ite1 (lq (plus h s) f) f (plus h s))
      (plus h s)
  end. 

(* tf7, singlepassNew, mainNew *)
Definition tf7 (l : List) : Nat := fst2 (tf5 l).
Definition singlepassNew (l : List) : Nat := tf7 l.
Definition mainNew (l : List) : Nat := singlepassNew l.

(* Theorem: the two mains are extensionally equal *)
Theorem optimize : forall inp0 : List,
    main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.
