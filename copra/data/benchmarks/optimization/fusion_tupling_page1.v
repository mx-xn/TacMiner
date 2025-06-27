(* -------------------------------------------------------------------- *)
(* Boolean and natural‐number types                                      *)
(* -------------------------------------------------------------------- *)
Inductive Bool : Type := TrueB | FalseB.

Inductive Nat : Type := Zero | Succ (n : Nat).

(* Addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* -------------------------------------------------------------------- *)
(* A simple binary tree over Nat                                        *)
(* -------------------------------------------------------------------- *)
Inductive Tree : Type :=
| Leaf : Nat -> Tree
| Node : Tree -> Tree -> Tree.

(* -------------------------------------------------------------------- *)
(* A unit type—needed for Nil                                             *)
(* -------------------------------------------------------------------- *)
(* A list of natural numbers *)
Inductive List : Type :=
| Nil  : List
| Cons : Nat -> List -> List.

(* -------------------------------------------------------------------- *)
(* Concatenation via tf0/tf1                                             *)
(* -------------------------------------------------------------------- *)
Require Import Coq.Program.Wf.

Fixpoint list_length (l : List) : nat :=
  match l with
  | Nil      => 0
  | Cons _ t => S (list_length t)
  end.

Fixpoint tf1 (l acc : List) :=
  match l with
  | Nil      => acc
  | Cons h t => Cons h (tf0 t acc)
  end
with tf0 (l acc : List) : List :=
  match l with
  | Nil      => acc
  | Cons h t => Cons h (tf1 t acc)
  end. 

(* tf0 is the same as tf1 *)

Definition cat (l1 l2 : List) : List := tf0 l1 l2.

(* -------------------------------------------------------------------- *)
(* less‐or‐equal on Nat returning Bool                                  *)
(* -------------------------------------------------------------------- *)
Fixpoint lq (n m : Nat) : Bool :=
  match n, m with
  | Zero,     Succ _  => TrueB
  | Zero,     Zero    => TrueB
  | Succ _,   Zero    => FalseB
  | Succ n',  Succ m' => lq n' m'
  end.

(* if‐then‐else yielding Nat *)
Definition ite2 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* maximum of two Nats *)
Definition maxn (n m : Nat) : Nat :=
  ite2 (lq n m) m n.

(* -------------------------------------------------------------------- *)
(* Depth‐of‐tree function                                               *)
(* -------------------------------------------------------------------- *)
Fixpoint depth (t : Tree) : Nat :=
  match t with
  | Leaf _    => Zero
  | Node l r  => plus (Succ Zero) (maxn (depth l) (depth r))
  end.

(* main = fst3 ∘ deepest                                         *)
(* -------------------------------------------------------------------- *)
(* A triple (list of deepest values, the Tree at which they occur)    *)
Inductive Tuple3 : Type :=
| MakeTuple3 : List -> Tree -> Tuple3.

Definition fst3 (p : Tuple3) : List :=
  match p with MakeTuple3 l _ => l end.

Definition snd3 (p : Tuple3) : Tree :=
  match p with MakeTuple3 _ t => t end.

(* equality on Nat *)
Fixpoint nateq (n m : Nat) : Bool :=
  match n, m with
  | Zero,     Zero    => TrueB
  | Zero,     Succ _  => FalseB
  | Succ _,   Zero    => FalseB
  | Succ n',  Succ m' => nateq n' m'
  end.

(* greater‐than on Nat *)
Fixpoint gq (n m : Nat) : Bool :=
  match n, m with
  | Zero,    _        => FalseB
  | Succ _, Zero      => TrueB
  | Succ n', Succ m'  => gq n' m'
  end.

(* Boolean if‐then‐else on Tuple3 *)
Definition ite3 (b : Bool) (x y : Tuple3) : Tuple3 :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

(* A single‐pass definition of 'deepest' via tf5 *)
Fixpoint tf5 (p t : Tree) : Tuple3 :=
  match t with
  | Leaf v =>
      (* at a leaf we record [v] as our current deepest list,
         and carry p (the "parent" Tree) for the second component *)
      MakeTuple3 (Cons v Nil) p
  | Node l r =>
      let p1 := tf5 p l in
      let p2 := tf5 p r in
      let d1 := depth (snd3 p1) in
      let d2 := depth (snd3 p2) in
      if gq d1 d2 then
        MakeTuple3 (fst3 p1) p
      else if nateq d1 d2 then
        MakeTuple3 (cat (fst3 p1) (fst3 p2)) p
      else
        MakeTuple3 (fst3 p2) p
  end.

Definition deepest (t : Tree) : Tuple3 := tf5 t t.

Definition main (t : Tree) : List := fst3 (deepest t).

(* -------------------------------------------------------------------- *)
(* A refined single‐pass that carries (list×depth) in one tuple         *)
(* -------------------------------------------------------------------- *)
Inductive Tuple4 : Type :=
| MakeTuple4 : List -> Nat -> Tuple4.

Definition fst4 (p : Tuple4) : List :=
  match p with MakeTuple4 l _ => l end.

Definition snd4 (p : Tuple4) : Nat :=
  match p with MakeTuple4 _ d => d end.

Definition ite4 (b : Bool) (x y : Tuple4) : Tuple4 :=
  match b with
  | TrueB  => x
  | FalseB => y
  end.

Fixpoint tf6 (t : Tree) : Tuple4 :=
  match t with
  | Leaf v =>
      MakeTuple4 (Cons v Nil) Zero
  | Node l r =>
      let p1 := tf6 l in
      let p2 := tf6 r in
      let f1 := fst4 p1 in
      let d1 := snd4 p1 in
      let f2 := fst4 p2 in
      let d2 := snd4 p2 in
      if gq d1 d2 then
        MakeTuple4 f1 (plus (Succ Zero) d1)
      else if nateq d1 d2 then
        MakeTuple4 (cat f1 f2) (plus d1 (Succ Zero))
      else
        MakeTuple4 f2 (plus d2 (Succ Zero))
  end.

Definition deepestNew (t : Tree) : Tuple4 := tf6 t.

Definition mainNew (t : Tree) : List := fst4 (deepestNew t).

(* -------------------------------------------------------------------- *)
(* The optimization equivalence theorem                                *)
(* -------------------------------------------------------------------- *)
Theorem optimize :
  forall inp0 : Tree,
    main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted. 