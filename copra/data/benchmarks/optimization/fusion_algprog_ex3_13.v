(* ################################################################# *)
(* Conversion of the given Isabelle definitions into Coq           *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(* Boolean, unit and natural‐number types                            *)
(* ----------------------------------------------------------------- *)

Inductive Bool : Type := 
  | TrueB 
  | FalseB.

Inductive Nat : Type := 
  | Zero 
  | Succ (n : Nat).

(* ----------------------------------------------------------------- *)
(* Lists of natural numbers, and “parameterized” lists (PList).      *)
(* ----------------------------------------------------------------- *)

Inductive List : Type :=
  | Nil  : List
  | Cons : Nat -> List -> List.

Inductive PList : Type :=
  | Pnil  : PList
  | Pcons : Nat -> (* “weight” *) 
            Nat -> (* “count‐so‐far” *)
            PList -> PList.

(* ----------------------------------------------------------------- *)
(* Addition and multiplication on our Nat                          *)
(* ----------------------------------------------------------------- *)

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

Fixpoint times (n m : Nat) : Nat :=
  match n with
  | Zero    => Zero
  | Succ n' => plus (times n' m) m
  end.

(* ----------------------------------------------------------------- *)
(* Build a PList from a List by
     • giving each element an initial “zero” key, then
     • incrementing the key of each cons‐cell by 1
     • propagating the tail via [tri] recursively
   This corresponds to the chain tf0/tf1/tf2/tf3 in Isabelle.      *)
(* ----------------------------------------------------------------- *)

Fixpoint tri (l : List) : PList :=
  match l with
  | Nil       => Pnil
  | Cons x xs   => 
      (* increment the head‐key by 1, carry over the old head in the “count” slot *)
      Pcons (plus x (Succ Zero)) x (tri xs)
  end.

(* ----------------------------------------------------------------- *)
(* Sum up a PList by multiplying key*count and adding over the spine *)
(* This is tf5/tf4/tsum in Isabelle.                                *)
(* ----------------------------------------------------------------- *)

Fixpoint tsum (pl : PList) : Nat :=
  match pl with
  | Pnil            => Zero
  | Pcons key cnt tl  => plus (times key cnt) (tsum tl)
  end.

(* ----------------------------------------------------------------- *)
(* The “old” main: build a PList via [tri], then sum it.             *)
(* ----------------------------------------------------------------- *)

Definition main (l : List) : Nat := tsum (tri l).

(* ----------------------------------------------------------------- *)
(* A fused version: produce in one pass a pair
     ( partial_sum : Nat,
       total_count : Nat )
   so that
     partial_sum = sum (times key count)
     total_count = sum of all counts = length l
   at each step, then extract the partial_sum as final result.
   This corresponds to triNew/tf6/tf7 in Isabelle.               *)
(* ----------------------------------------------------------------- *)

Inductive Tuple2 : Type :=
  | MakeTuple2 : Nat -> Nat -> Tuple2.

Definition fst2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 a _ => a end.

Definition snd2 (t : Tuple2) : Nat :=
  match t with MakeTuple2 _ b => b end.

Fixpoint triNew (l : List) : Tuple2 :=
  match l with
  | Nil     => MakeTuple2 Zero Zero
  | Cons x xs  =>
      let p := triNew xs in
      let sum_so_far   := fst2 p in
      let count_so_far := snd2 p in
      (* we treat x as “count increment” for the second component,
         and as “key” for the first component multiplied by count_so_far+1 *)
      MakeTuple2
        (plus sum_so_far   (* old sum *)
              (* add current contribution: x * (count_so_far + 1) *)
              (times x (Succ count_so_far)))
        (Succ count_so_far)  (* new count *)
  end.

Definition mainNew (l : List) : Nat :=
  fst2 (triNew l).

(* ----------------------------------------------------------------- *)
(* The correctness theorem                                            *)
(* ----------------------------------------------------------------- *)

Theorem optimize : forall inp0 : List,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.
