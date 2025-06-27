(* Custom Boolean type *)
Inductive Bool : Type :=
| TrueB
| FalseB.

Definition negb (b : Bool) : Bool :=
  match b with
  | TrueB  => FalseB
  | FalseB => TrueB
  end.

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

(* Custom natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* List of Nat *)
Inductive List : Type :=
| Nil
| Cons (h : Nat) (t : List).

(* tf0 rebuilds its input list *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil       => Nil
  | Cons h t  => Cons h (tf0 t)
  end.

(* tf1 x l2 = x if l2 = Nil, else Cons h (tf0 t) *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil      => x
  | Cons h t => Cons h (tf0 t)
  end.

(* less-or-equal on Nat, returning Bool *)
Fixpoint lq (x y : Nat) : Bool :=
  match x, y with
  | Zero, Succ _     => TrueB
  | Zero, Zero       => TrueB
  | Succ _, Zero     => FalseB
  | Succ x', Succ y' => lq x' y'
  end.

(* if-then-else yielding Nat *)
Definition ite1 (b : Bool) (u v : Nat) : Nat :=
  match b with
  | TrueB  => u
  | FalseB => v
  end.

(* max on Nat *)
Definition maxn (x y : Nat) : Nat :=
  ite1 (lq x y) y x.

(* addition on Nat *)
Fixpoint plusn (x y : Nat) : Nat :=
  match x with
  | Zero   => y
  | Succ x' => Succ (plusn x' y)
  end.

(* mis computes the maximal prefix-sum etc. via two accumulators *)
Fixpoint tf4 (acc1 acc2 : Nat) (l : List) : Nat :=
  match l with
  | Nil        => maxn acc2 acc1
  | Cons h t   =>
      (* swap accumulators as per tf3 = tf4 b a l *)
      tf4 (plusn h acc1) (maxn acc2 acc1) t
  end.

Definition mis (l : List) : Nat :=
  tf4 Zero Zero l.

Definition tf2 (l : List) : Nat :=
  mis (tf0 l).

Definition singlepass (l : List) : Nat :=
  tf2 l.

Definition main (l : List) : Nat :=
  singlepass l.

(* Tuple of two Nats *)
Inductive Tuple2 : Type :=
| MakeTuple2 (fst snd : Nat).

Definition fst2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 x _ => x end.

Definition snd2 (p : Tuple2) : Nat :=
  match p with MakeTuple2 _ y => y end.

(* tf6 builds a Tuple2 by scanning the list *)
Fixpoint tf6 (l : List) : Tuple2 :=
  match l with
  | Nil       => MakeTuple2 Zero Zero
  | Cons h t  =>
      let p := tf5 t in
      let f := fst2 p in
      let s := snd2 p in
      let newf :=
        ite1 (lq f (plusn h s))
             (plusn h s)
             f
      in
      MakeTuple2 newf f
  end
  with tf5 (l : List) : Tuple2 :=
  match l with
  | Nil       => MakeTuple2 Zero Zero
  | Cons h t  =>
      let p := tf6 t in
      let f := fst2 p in
      let s := snd2 p in
      let newf :=
        ite1 (lq f (plusn h s))
             (plusn h s)
             f
      in
      MakeTuple2 newf f
  end.

Definition tf7 (l : List) : Nat :=
  fst2 (tf5 l).

Definition singlepassNew (l : List) : Nat :=
  tf7 l.

Definition mainNew (l : List) : Nat :=
  singlepassNew l.

(* Theorem stating the equivalence of both traversals *)
Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted. 