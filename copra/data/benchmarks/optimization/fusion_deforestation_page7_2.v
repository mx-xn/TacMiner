(* Custom Boolean type *)
Inductive Bool : Type :=
| TrueB
| FalseB.

(* Custom natural numbers *)
Inductive Nat : Type :=
| Zero
| Succ (n : Nat).

(* Addition on Nat *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | Zero    => m
  | Succ n' => Succ (plus n' m)
  end.

(* Multiplication on Nat *)
Fixpoint times (n m : Nat) : Nat :=
  match n with
  | Zero    => Zero
  | Succ n' => plus (times n' m) m
  end.

(* Square of a Nat *)
Definition square (n : Nat) : Nat := times n n.

(* A binary tree over Nat *)
Inductive Tree : Type :=
| Leaf   (n : Nat)
| Branch (l r : Tree).

(* squaretr: square every leaf in the tree *)
Fixpoint squaretr (t : Tree) : Tree :=
  match t with
  | Leaf n       => Leaf (square n)
  | Branch l r   => Branch (squaretr l) (squaretr r)
  end.

(* sumtr: sum all leaves in the tree *)
Fixpoint sumtr (t : Tree) : Nat :=
  match t with
  | Leaf n       => n
  | Branch l r   => plus (sumtr l) (sumtr r)
  end.

(* main = sumtr ∘ squaretr *)
Definition main (t : Tree) : Nat := sumtr (squaretr t).

(* mainNew: directly sum of squares of leaves *)
Fixpoint mainNew (t : Tree) : Nat :=
  match t with
  | Leaf n       => square n
  | Branch l r   => plus (mainNew l) (mainNew r)
  end.

(* The optimization theorem *)
Theorem optimize : forall t : Tree,
  main t = mainNew t.
Proof.
  induction t as [n | l IHl r IHr].
  - (* Leaf case *) reflexivity.
Admitted. 