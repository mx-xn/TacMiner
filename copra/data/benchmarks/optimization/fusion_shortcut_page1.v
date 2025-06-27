(* Custom Boolean type                                                  *)
(* -------------------------------------------------------------------- *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* Boolean “and” *)
Definition andb (x y : Bool) : Bool :=
  match x, y with
  | TrueB, TrueB => TrueB
  | _, _         => FalseB
  end.

(* -------------------------------------------------------------------- *)
(* Custom Peano-style natural numbers                                   *)
(* -------------------------------------------------------------------- *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* -------------------------------------------------------------------- *)
(* A list of Nats                                                      *)
(* -------------------------------------------------------------------- *)
Inductive List : Type :=
| Nil
| Cons (h : Nat) (t : List).

(* -------------------------------------------------------------------- *)
(* A list of Bools                                                     *)
(* -------------------------------------------------------------------- *)
Inductive BoolList : Type :=
| Bnil
| Bcons (b : Bool) (bs : BoolList).

(* -------------------------------------------------------------------- *)
(* geq x y = “x ≥ y”                                                    *)
(*   geq Zero    (Succ _) = FalseB                                      *)
(*   geq _       Zero     = TrueB                                      *)
(*   geq (Succ x) (Succ y) = geq x y                                    *)
(* -------------------------------------------------------------------- *)
Fixpoint geq (x y : Nat) : Bool :=
  match x, y with
  | Zero,    Succ _   => FalseB
  | _,       Zero     => TrueB
  | Succ x', Succ y'  => geq x' y'
  end.

(* p n = (0 ≥ n) *)
Definition p (n : Nat) : Bool := geq Zero n.

(* -------------------------------------------------------------------- *)
(* mapbl: List → BoolList                                               *)
(*   mapbl Nil        = Bnil                                           *)
(*   mapbl (Cons n ns) = Bcons (p n) (mapbl ns)                        *)
(* -------------------------------------------------------------------- *)
Fixpoint mapbl (l : List) : BoolList :=
  match l with
  | Nil        => Bnil
  | Cons n ns  => Bcons (p n) (mapbl ns)
  end.

(* -------------------------------------------------------------------- *)
(* allbl: BoolList → Bool                                               *)
(*   allbl Bnil        = TrueB                                         *)
(*   allbl (Bcons b bs) = andb b (allbl bs)                            *)
(* -------------------------------------------------------------------- *)
Fixpoint allbl (bs : BoolList) : Bool :=
  match bs with
  | Bnil        => TrueB
  | Bcons b bs' => andb b (allbl bs')
  end.

(* main = allbl ∘ mapbl *)
Definition main (l : List) : Bool := allbl (mapbl l).

(* -------------------------------------------------------------------- *)
(* lq x y = “x < y” (strict)                                           *)
(*   lq Zero    (Succ _) = TrueB                                       *)
(*   lq _       Zero     = FalseB                                      *)
(*   lq (Succ x) (Succ y) = lq x y                                     *)
(* -------------------------------------------------------------------- *)
Fixpoint lq (x y : Nat) : Bool :=
  match x, y with
  | Zero,    Succ _   => TrueB
  | _,       Zero     => FalseB
  | Succ x', Succ y'  => lq x' y'
  end.

(* -------------------------------------------------------------------- *)
(* tf4 = “all elements of l satisfy lq n 1”                            *)
(*   tf4 Nil        = TrueB                                            *)
(*   tf4 (Cons n ns) = andb (tf4 ns) (lq n (Succ Zero))               *)
(* -------------------------------------------------------------------- *)
Fixpoint tf4 (l : List) : Bool :=
  match l with
  | Nil        => TrueB
  | Cons n ns  => andb (tf4 ns) (lq n (Succ Zero))
  end.

(* mainNew = tf4 *)
Definition mainNew (l : List) : Bool := tf4 l.

(* -------------------------------------------------------------------- *)
(* Theorem: the two definitions coincide                                *)
(* -------------------------------------------------------------------- *)
Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.  