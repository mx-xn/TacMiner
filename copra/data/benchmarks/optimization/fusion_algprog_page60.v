(* Coq translation of the given Isabelle definitions *)

(* -------------------------------------------------------------------- *)
(* Boolean type                                                          *)
(* -------------------------------------------------------------------- *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* -------------------------------------------------------------------- *)
(* Custom natural numbers                                                 *)
(* -------------------------------------------------------------------- *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* op : Nat → Nat, increment by one *)
Definition op (n : Nat) : Nat := plus (Succ Zero) n.

(* comparison ≤ on Nat returning Bool *)
Fixpoint lq (x y : Nat) : Bool :=
  match x, y with
  | Zero,    Succ _  => TrueB
  | Zero,    Zero    => TrueB
  | Succ _,  Zero    => FalseB
  | Succ x', Succ y' => lq x' y'
  end.

(* if‐then‐else for Nat results *)
Definition ite1 (b : Bool) (u v : Nat) : Nat :=
  match b with
  | TrueB  => u
  | FalseB => v
  end.

(* maximum of two Nat *)
Definition maxn (x y : Nat) : Nat :=
  ite1 (lq x y) y x.

(* -------------------------------------------------------------------- *)
(* A binary tree over Nat                                               *)
(* -------------------------------------------------------------------- *)
Inductive Tree : Type :=
| Tip (n : Nat)
| Bin (l r : Tree).

(* -------------------------------------------------------------------- *)
(* tf2 and tf3 : Tree → Tree, mutually recursive                        *)
(*    tf3 (Tip n)   = Tip (op n)                                        *)
(*    tf3 (Bin l r) = Bin (tf2 l) (tf2 r)                               *)
(*    tf2 = tf3                                                     *)
(* -------------------------------------------------------------------- *)
Fixpoint tf3 (t : Tree) : Tree :=
  match t with
  | Tip n    => Tip (op n)
  | Bin l r  => Bin (tf2 l) (tf2 r)
  end
with tf2 (t : Tree) : Tree := 
  match t with
  | Tip n   => Tip (op n)
  | Bin l r => Bin (tf3 l) (tf3 r)
  end. 

(* -------------------------------------------------------------------- *)
(* tf1, tf0, tri : Tree → Tree                                          *)
(*    tf1 (Tip n)   = Tip Zero                                         *)
(*    tf1 (Bin l r) = Bin (tf2 (tf0 l)) (tf2 (tf0 r))                   *)
(*    tf0 = tf1                                                       *)
(*    tri = tf0                                                       *)
(* -------------------------------------------------------------------- *)
Fixpoint tf1 (t : Tree) : Tree :=
  match t with
  | Tip _     => Tip Zero
  | Bin l r   => Bin (tf2 (tf0 l)) (tf2 (tf0 r))
  end
with tf0 (t : Tree) : Tree := 
  match t with
  | Tip _     => Tip Zero
  | Bin l r   => Bin (tf2 (tf1 l)) (tf2 (tf1 r))
  end.

(* tf0 = tf1, and tri = tf0 *)
Definition tri := tf0.

(* -------------------------------------------------------------------- *)
(* tf5 and tf4 : Tree → Nat, mutually recursive                        *)
(*    tf5 (Tip n)   = n                                               *)
(*    tf5 (Bin l r) = maxn (tf4 l) (tf4 r)                             *)
(*    tf4 = tf5                                                       *)
(* maximum = tf4                                                      *)
(* -------------------------------------------------------------------- *)
Fixpoint tf5 (t : Tree) : Nat :=
  match t with
  | Tip n    => n
  | Bin l r  => maxn (tf4 l) (tf4 r)
  end
with tf4 (t : Tree) : Nat := 
  match t with
  | Tip n    => n
  | Bin l r  => maxn (tf5 l) (tf5 r)
  end.  

Definition maximum := tf4. 

(* main = maximum ∘ tri *)
Definition main (t : Tree) : Nat := maximum (tri t).

(* -------------------------------------------------------------------- *)
(* tf7 and tf6 : Tree → Nat, mutually recursive                        *)
(*    tf7 (Tip n)   = Zero                                             *)
(*    tf7 (Bin l r) = ite1 (lq (tf6 l) (tf6 r))
                          (plus (Succ Zero) (tf6 r))
                          (plus (Succ Zero) (tf6 l)) *)
(*    tf6 = tf7                                                       *)
(* triNew = tf6                                                      *)
(* mainNew = triNew                                                  *)
(* -------------------------------------------------------------------- *)
Fixpoint tf7 (t : Tree) : Nat :=
  match t with
  | Tip _    => Zero
  | Bin l r  =>
     let vl := tf6 l in
     let vr := tf6 r in
     ite1 (lq vl vr)
          (plus (Succ Zero) vr)
          (plus (Succ Zero) vl)
  end
with tf6 (t : Tree) : Nat := 
  match t with
  | Tip _    => Zero
  | Bin l r  =>
     let vl := tf7 l in
     let vr := tf7 r in
     ite1 (lq vl vr)
          (plus (Succ Zero) vr)
          (plus (Succ Zero) vl)
  end.

(* tf6 is the main function, and tf7 is the auxiliary one *)

(* triNew = tf6, mainNew = triNew *)

Definition triNew := tf6.
Definition mainNew (t : Tree) : Nat := triNew t.

(* -------------------------------------------------------------------- *)
(* The optimization theorem                                             *)
(* -------------------------------------------------------------------- *)
Theorem optimize : forall inp0 : Tree,
  main inp0 = mainNew inp0.
Proof.
  intros.
  (* proof omitted *)
Admitted.