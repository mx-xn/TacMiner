(* Boolean type *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

(* A simple list of natural numbers *)
Inductive List : Type :=
| Nil  : List
| Cons : Nat -> List -> List.

(* tf0 rebuilds its input list *)
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

(* less‐than on our Nat: lq n m = TrueB iff n < m *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero,     Succ _   => TrueB
  | Succ _,   Zero     => FalseB
  | Succ n',  Succ m'  => lq n' m'
  | Zero,     Zero     => FalseB
  end.

(* addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* conditional returning a Nat *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* tf4: one‐pass computation over the list *)
Fixpoint tf4 (l : List) : Nat :=
  match l with
  | Nil => Zero
  | Cons h t =>
    let v := plus (tf3 t) h in
    ite1 (lq Zero v) Zero v
  end
  with tf3 (l : List) : Nat :=
    match l with
    | Nil => Zero
    | Cons h t =>
      let v := plus (tf4 t) h in
      ite1 (lq Zero v) Zero v
    end.

(* mps = “main pass” *)
Definition mps (l : List) : Nat := tf3 l.

(* tf2 and singlepass = mps ∘ tf0 *)
Definition tf2 (l : List) : Nat := mps (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* tf6: alternative one‐pass over the list *)
Fixpoint tf6 (l : List) : Nat :=
  match l with
  | Nil        => Zero
  | Cons h t   =>
    let v := plus h (tf5 t) in
    (* if v < 0 then v else Zero *)
    if lq v Zero
    then v
    else Zero
  end
  with tf5 (l : List) : Nat :=
    match l with
    | Nil        => Zero
    | Cons h t   =>
      let v := plus h (tf6 t) in
      (* if v < 0 then v else Zero *)
      if lq v Zero
      then v
      else Zero
    end.

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
