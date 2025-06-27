Require Export ZArith.

Theorem div2_rect (P: nat -> Type) :
 P 0 -> P 1 ->
 (forall n, P n -> P (S n) -> P(S (S n)))->
 forall n:nat, P n.
Proof.
 intros H0 H1 H n; assert (X: ( P n * P (S n))%type).
 - induction n; intuition.
 - now destruct X.
Defined.

Open Scope Z_scope.
Fixpoint div_bin (n m:positive){struct n} : Z*Z :=
 match n with
 | 1%positive => match m with 1%positive =>(1,0) | _ =>(0,1) end
 | xO n' =>
   let (q',r'):=div_bin n' m in
   match Z_lt_ge_dec (2*r')(Zpos m) with
   | left Hlt => (2*q', 2*r')
   | right Hge => (2*q' + 1, 2*r' - (Zpos m))
   end
 | xI n' =>
   let (q',r'):=div_bin n' m in
   match Z_lt_ge_dec (2*r' + 1)(Zpos m) with
   | left Hlt => (2*q', 2*r' + 1)
   | right Hge => (2*q' + 1, (2*r' + 1)-(Zpos m))
   end
 end.

 Close Scope Z_scope. 

Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
   [intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r' + 1)(Zpos arg2)); intros H
   | intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r')(Zpos arg2)); intros H
   | case arg2; lazy beta iota delta [div_bin]; intros].

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive occ (n:Z) : Z_btree -> Prop :=
| occ_root : forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
| occ_l : forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
| occ_r : forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2)
.

Derive Inversion_clear OCC_INV with
    (forall (z z':Z) (t1 t2:Z_btree), occ z' (Z_bnode z t1 t2)).

#[ export ] Hint  Constructors   occ  : searchtrees.

Lemma occ_inv :
  forall (z z':Z) (t1 t2:Z_btree),
    occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
  inversion 1 using OCC_INV; auto with searchtrees.
Qed.

#[ export ] Hint Resolve occ_inv: searchtrees.

Open Scope Z_scope.

Inductive min (z:Z) (t:Z_btree) : Prop :=
| min_intro : (forall z':Z, occ z' t -> z < z') -> min z t.

#[ export ] Hint Constructors min: searchtrees.

(* z is greater than every label in t *)
Inductive maj (z:Z) (t:Z_btree) : Prop :=
  maj_intro : (forall z':Z, occ z' t -> z' < z) -> maj z t
.

#[ export ] Hint Constructors maj: searchtrees.
Inductive search_tree : Z_btree -> Prop :=
| leaf_search_tree : search_tree Z_leaf
| bnode_search_tree :
    forall (z:Z) (t1 t2:Z_btree),
      search_tree t1 ->
      search_tree t2 ->
      maj z t1 -> min z t2 -> search_tree (Z_bnode z t1 t2). 

Section st. 
  Variable n : Z.
  Variables t1 t2 : Z_btree.
  Hypothesis se : search_tree (Z_bnode n t1 t2).

  Lemma min_r : min n t2.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve min_r: searchtrees.
End st. 
Close Scope Z_scope. 