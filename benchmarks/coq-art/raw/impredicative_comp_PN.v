
(** BEGIN_DREAMPROVER_TACTICS **)
Ltac custom_tac0 H0 := unfold H0; auto.
Ltac custom_tac1 H0 := apply H0; auto.
(** END_DREAMPROVER_TACTICS **)

Require Export List Relations.

Section R_declared.

Variables (A: Type)
            (R: relation A).

Inductive sorted : list A -> Prop :=
    sorted0 : sorted  nil
  | sorted1 : forall x:A, sorted  (x::nil)
  | sorted2 : forall (x1 x2:A)(l':list A),
      R x1 x2 -> sorted  (x2::l') -> sorted  (x1::x2::l').

#[local] Hint Constructors sorted : core.

Definition impredicative_sorted (l:list A) : Prop :=
    forall P :  list A -> Prop,
      P nil ->
      (forall x:A, P (x::nil))->
      (forall (x1 x2:A)(l':list A),
          R x1 x2 -> P (x2::l') -> P (x1::x2::l'))->
      P l.

Theorem isorted0  :  impredicative_sorted nil.
Proof. red; intros; assumption. Qed.

Theorem isorted1 :  forall  x: A , impredicative_sorted (x::nil).
Proof. custom_tac0 impredicative_sorted. Qed.

Theorem isorted2  :
    forall (x1 x2:A)(l':list A),
      R x1 x2 ->
      impredicative_sorted  (x2::l') ->
      impredicative_sorted  (x1::x2::l').
Proof. intros x1 x2 l' Hr Hs P Hsn Hs1 Hs2. 
    custom_tac1 Hs2. apply Hs; auto. Qed.

#[local] Hint Resolve isorted0 isorted1 isorted2 : core.

Theorem sorted_to_impredicative_sorted :
    forall l, sorted  l -> impredicative_sorted l.
Proof. induction 1; auto. Qed.

Theorem impredicative_sorted_to_sorted :
    forall l, impredicative_sorted  l -> sorted  l.
Proof. intros l H; custom_tac1 H. Qed.

End R_declared.

Arguments sorted {A} R _.

Arguments impredicative_sorted {A} R _.

Definition impredicative_le (n p:nat) : Prop :=
  forall P: nat -> Prop,
    P n ->
    (forall m:nat, P m -> P (S m)) ->
    P p.

Theorem impredicative_le_n : forall n: nat, impredicative_le n n.
Proof. custom_tac0 impredicative_le. Qed.

Theorem impredicative_le_S : 
  forall n m:nat, impredicative_le n m -> impredicative_le n (S m).
Proof. intros n m Hle P Hn Hs; apply Hs; apply Hle; auto. Qed.

#[export] Hint Resolve impredicative_le_n impredicative_le_S : core.

Theorem le_to_impredicative :
  forall n p, n <= p -> impredicative_le n p.
Proof. intros n p Hle; elim Hle; auto. Qed.

Theorem impredicative_to_le :
  forall n p, impredicative_le n p -> n <= p.
Proof. intros n p H; apply H; auto. Qed.

Definition impredicative_or (A B:Prop) : Prop :=
  forall P:Prop, 
    
    (A -> P) ->
    
    (B -> P) ->
    P.

Theorem impredicative_or_intro1 :
  forall A B:Prop, A -> impredicative_or A B.
Proof. custom_tac0 impredicative_or. Qed.

Theorem impredicative_or_intro2 :
  forall A B:Prop, B -> impredicative_or A B.
Proof. custom_tac0 impredicative_or. Qed.

#[export] Hint Resolve impredicative_or_intro1 impredicative_or_intro2 : core.

Theorem or_to_impredicative : forall A B, A \/ B -> impredicative_or A B.
Proof. intros A B H; elim H; auto. Qed.

Theorem impredicative_to_or : forall A B, impredicative_or A B -> A \/ B.
Proof. intros A B H; apply H; auto. Qed.

