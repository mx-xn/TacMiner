(* Coq translation of the Isabelle development *)

(* -------------------------------------------------------------------- *)
(* Boolean type (not used below, but kept for faithfulness)             *)
(* -------------------------------------------------------------------- *)
Inductive Bool : Type := 
  | TrueB 
  | FalseB.

(* -------------------------------------------------------------------- *)
(* A simple Peano‐style natural number type                             *)
(* -------------------------------------------------------------------- *)
Inductive Nat : Type :=
  | Zero 
  | Succ (n : Nat).

(* addition and multiplication on our Nat *)
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

(* -------------------------------------------------------------------- *)
(* A binary tree over Nat                                              *)
(* -------------------------------------------------------------------- *)
Inductive Tree : Type :=
  | Tip (n : Nat)
  | Bin (l r : Tree).

(* -------------------------------------------------------------------- *)
(* A 1‐tuple of Nat × Nat                                               *)
(* -------------------------------------------------------------------- *)
Inductive Tuple1 : Type := MakeTuple1 (fst1 : Nat) (snd1 : Nat).

Definition fst1_of (t : Tuple1) : Nat :=
  match t with MakeTuple1 x _ => x end.

Definition snd1_of (t : Tuple1) : Nat :=
  match t with MakeTuple1 _ y => y end.

(* -------------------------------------------------------------------- *)
(* An intermediate PTree type                                           *)
(* -------------------------------------------------------------------- *)
Inductive PTree : Type :=
  | Ptip (a b : Nat)
  | Pbin (l r : PTree).

(* tf3 and tf2 : PTree → PTree, mutually recursive *)
Fixpoint tf3 (t : PTree) : PTree :=
  match t with
  | Ptip a b   => Ptip (plus a (Succ Zero)) b
  | Pbin l r   => Pbin (tf2 l) (tf2 r)
  end
with tf2 (t : PTree) : PTree := 
  match t with
  | Ptip a b   => Ptip (plus a Zero) b
  | Pbin l r   => Pbin (tf3 l) (tf3 r)
  end.

(* tf1 : Tree → PTree *)
Fixpoint tf1 (t : Tree) : PTree :=
  match t with
  | Tip n     => Ptip Zero n
  | Bin l r   => Pbin (tf2 (tf1 l)) (tf2 (tf1 r))
  end.

(* tf0 = tf1, and tri = tf0 *)
Definition tf0 := tf1.
Definition tri := tf0.

(* tf5 and tf4 : PTree → Nat, mutually recursive *)
Fixpoint tf5 (t : PTree) : Nat :=
  match t with
  | Ptip a b => times a b
  | Pbin l r => plus (tf4 l) (tf4 r)
  end
with tf4 (t : PTree) : Nat := 
  match t with
  | Ptip a b => plus (times a b) (Succ Zero)
  | Pbin l r => plus (tf5 l) (tf5 r)
  end.

(* tf4 is the main function, and tf5 is the auxiliary one *)
(* Note: this is not the same as in the Isabelle version! *)

(* tsum = tf4, and main = tsum ∘ tri *)
Definition tsum := tf4.
Definition main (t : Tree) : Nat := tsum (tri t).

(* tf7 and tf6 : Tree → Tuple1, mutually recursive *)
Fixpoint tf7 (t : Tree) : Tuple1 :=
  match t with
  | Tip n   => MakeTuple1 Zero n
  | Bin l r =>
    let p1 := tf6 l in
    let p2 := tf6 r in
    let a1 := fst1_of p1 in
    let b1 := snd1_of p1 in
    let a2 := fst1_of p2 in
    let b2 := snd1_of p2 in
    MakeTuple1
      (plus (plus (plus a1 b1) a2) b2)
      (plus b1 b2)
  end
with tf6 (t : Tree) : Tuple1 := 
  match t with
  | Tip n   => MakeTuple1 Zero n
  | Bin l r =>
    let p1 := tf7 l in
    let p2 := tf7 r in
    let a1 := fst1_of p1 in
    let b1 := snd1_of p1 in
    let a2 := fst1_of p2 in
    let b2 := snd1_of p2 in
    MakeTuple1
      (plus (plus (plus a1 b1) a2) b2)
      (plus b1 b2)
  end.

(* tf6 is the main function, and tf7 is the auxiliary one *)

(* triNew = tf7, mainNew = fst1_of ∘ triNew *)
Definition triNew := tf7.
Definition mainNew (t : Tree) : Nat := fst1_of (triNew t).

(* -------------------------------------------------------------------- *)
(* The optimization theorem                                             *)
(* -------------------------------------------------------------------- *)
Theorem optimize : forall (inp0 : Tree),
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted. 