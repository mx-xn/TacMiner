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
  | TrueB, _     => TrueB
  | _, TrueB     => TrueB
  | FalseB, FalseB => FalseB
  end.

Definition ite1 (b y : Bool) : Bool :=
  match b with
  | TrueB  => TrueB
  | FalseB => y
  end.

(* Unit type *)
Inductive Unit : Type := 
| Null.

(* List type *)
Inductive List : Type :=
| Nil  : Unit -> List
| Cons : Bool -> List -> List.

(* tf0: simply traverse and rebuild the list — this is structurally recursive on [l]. *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil _      => l
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1: returns [x] on an empty list, otherwise rebuilds like tf0 *)
Definition tf1 (x l2 : List) : List :=
  match l2 with
  | Nil _    => x
  | Cons h t => Cons h (tf0 t)
  end.

(* tf2 and singlepass *)
Fixpoint tf3 (b : Bool) (l : List) : Bool :=
  match l with
  | Nil _      => FalseB
  | Cons h t   => ite1 (andb b (negb h)) (tf3 (orb b h) t)
  end.

Definition zafter1 (l : List) : Bool := tf3 FalseB l.

Definition tf2 (l : List) : Bool := zafter1 (tf0 l).

Definition singlepass (l : List) : Bool := tf2 l.

Definition main (l : List) : Bool := singlepass l.

(* Tuple2 and projections *)
Inductive Tuple2 : Type :=
| MakeTuple2 : Bool -> Bool -> Tuple2.

Definition fst2 (t : Tuple2) : Bool :=
  match t with MakeTuple2 x _ => x end.

Definition snd2 (t : Tuple2) : Bool :=
  match t with MakeTuple2 _ y => y end.

(* tf5 and tf6 without mutual recursion: tf6 calls tf5 *)
Fixpoint tf5 (l : List) : Tuple2 :=
  match l with
  | Nil _      => MakeTuple2 FalseB TrueB
  | Cons h t   =>
      let p := tf5 t in
      MakeTuple2
        (orb (andb h (negb (snd2 p))) (fst2 p))
        (andb h (snd2 p))
  end.

Definition tf7 (l : List) : Bool := fst2 (tf5 l).

Definition singlepassNew (l : List) : Bool := tf7 l.

Definition mainNew (l : List) : Bool := singlepassNew l.

(* Optimize theorem *)
Theorem optimize : forall inp0 : List, main inp0 = mainNew inp0.
Proof.
  intros. 
  (* proof omitted *) 
Admitted.