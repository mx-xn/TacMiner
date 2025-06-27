(* Types *)

Inductive Bool : Type :=
| TrueB
| FalseB.

Inductive Nat : Type :=
| Zero
| Succ (_ : Nat).

Inductive List : Type :=
| Nil
| Cons (_ : Nat) (_ : List).

(* tf0: traverse and rebuild the list (identity) *)
Fixpoint tf0 (l : List) : List :=
  match l with
  | Nil        => Nil
  | Cons h t   => Cons h (tf0 t)
  end.

(* tf1 x l = x if l = Nil, otherwise rebuild l via tf0 *)
Definition tf1 (x l : List) : List :=
  match l with
  | Nil       => x
  | Cons h t  => Cons h (tf0 t)
  end.

(* A standard length function *)
Fixpoint length (l : List) : Nat :=
  match l with
  | Nil       => Zero
  | Cons _ t  => Succ (length t)
  end.

(* tf2 = length ∘ tf0 *)
Definition tf2 (l : List) : Nat := length (tf0 l).

Definition singlepass := tf2.

Definition main := singlepass.

(* plus: unary “increment‐by‐one” on Nat *)
Fixpoint plus (n : Nat) : Nat :=
  match n with
  | Zero    => Succ Zero
  | Succ x  => Succ (plus x)
  end.

(* tf6: another way to compute length, using plus *)
Fixpoint tf6 (l : List) : Nat :=
  match l with
  | Nil       => Zero
  | Cons _ t  => plus (tf5 t)
  end
with tf5 (l : List) : Nat := 
  match l with
  | Nil       => Zero
  | Cons _ t  => plus (tf6 t)
  end.

Definition tf7 (l : List) : Nat := 
  match l with
  | Nil       => Zero
  | Cons _ t  => tf5 l
  end. 

Definition singlepassNew := tf7.

Definition mainNew := singlepassNew.

(* Theorem: both versions agree *)
Theorem optimize : forall inp0 : List,
    main inp0 = mainNew inp0.
Proof.
  intros. 
Admitted. 