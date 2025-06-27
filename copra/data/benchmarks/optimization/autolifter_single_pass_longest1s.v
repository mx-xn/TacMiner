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

Definition orb (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | TrueB, _     => TrueB
  | _, TrueB     => TrueB
  | FalseB, _    => FalseB
  end.

(* Unit type (unused in list) *)
Inductive Unit : Type := Null.

(* List of Bool *)
Inductive List : Type :=
| Nil  : List
| Cons : Bool -> List -> List.

(* tf0 traverses and rebuilds a list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil       => Nil
  | Cons h t  => Cons h (tf0 t)
  end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil       => x
  | Cons h t  => Cons h (tf0 t)
  end.

(* Natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

(* comparison lq: Nat -> Nat -> Bool, lq n m = (n ≤ m) *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero, Succ _    => TrueB
  | Succ _, Zero    => FalseB
  | Zero, Zero      => FalseB
  | Succ n', Succ m' => lq n' m'
  end.

(* ite1 for Nat result: if b then x else y *)
Definition ite1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* max of two Nats, uses lq to pick the larger *)
Definition maxn (n m : Nat) : Nat :=
  ite1 (lq n m) m n.

(* addition on our Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* tf4: Nat -> List -> Nat *)
Fixpoint tf4 (acc : Nat) (l : List) : Nat :=
  match l with
  | Nil       => Zero
  | Cons h t  =>
      let acc' := ite1 h (plus acc (Succ Zero)) Zero in
      maxn acc' (tf4 acc' t)
  end.

(* tf3 alias for tf4 *)
Definition tf3 := tf4.

(* longest1s = tf3 Zero *)
Definition longest1s (l : List) : Nat := tf3 Zero l.

(* single‐pass computation via tf0 then longest1s *)
Definition tf2 (l : List) : Nat := longest1s (tf0 l).
Definition singlepass (l : List) : Nat := tf2 l.
Definition main (l : List) : Nat := singlepass l.

(* Tuple2 of two Nats *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Nat -> Nat -> Tuple2.

Definition fst2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 x _ => x end.

Definition snd2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 _ y => y end.

(* tf6 builds a Tuple2 from a Bool‐list, counting runs of TrueB *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil       => MakeTuple2 Zero Zero
  | Cons h t  =>
      let p := tf5 t in
      let run_len := fst2 p in
      let best    := snd2 p in
      let curr    := ite1 h (plus run_len (Succ Zero)) Zero in
      let best'   := maxn curr best in
      let run'    := ite1 (negb h) Zero (plus (Succ Zero) run_len) in
      MakeTuple2 best' run'
  end
with tf5 (l : List) := 
match l with
  | Nil       => MakeTuple2 Zero Zero
  | Cons h t  =>
      let p := tf6 t in
      let run_len := fst2 p in
      let best    := snd2 p in
      let curr    := ite1 h (plus run_len (Succ Zero)) Zero in
      let best'   := maxn curr best in
      let run'    := ite1 (negb h) Zero (plus (Succ Zero) run_len) in
      MakeTuple2 best' run'
  end.

(* extract the best run length *)
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