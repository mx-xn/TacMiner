(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(** * NMake_gen *)

(** From a cyclic Z/nZ representation to arbitrary precision natural numbers.*)

(** Remark: File automatically generated by NMake_gen.ml, DO NOT EDIT ! *)

Require Import BigNumPrelude ZArith Lia Ndigits CyclicAxioms
 DoubleType DoubleMul DoubleDivn1 DoubleBase DoubleCyclic Nbasic
 Wf_nat StreamMemo.

Local Close Scope Z.

Module Make (W0:CyclicType) <: NAbstract.

 (** * The word types *)

 Local Notation w0 := W0.t.
 Definition w1 := zn2z w0.
 Definition w2 := zn2z w1.
 Definition w3 := zn2z w2.
 Definition w4 := zn2z w3.
 Definition w5 := zn2z w4.
 Definition w6 := zn2z w5.

 (** * The operation type classes for the word types *)

 Local Notation w0_op := W0.ops.
 Instance w1_op : ZnZ.Ops w1 := mk_zn2z_ops w0_op.
 Instance w2_op : ZnZ.Ops w2 := mk_zn2z_ops w1_op.
 Instance w3_op : ZnZ.Ops w3 := mk_zn2z_ops w2_op.
 Instance w4_op : ZnZ.Ops w4 := mk_zn2z_ops_karatsuba w3_op.
 Instance w5_op : ZnZ.Ops w5 := mk_zn2z_ops_karatsuba w4_op.
 Instance w6_op : ZnZ.Ops w6 := mk_zn2z_ops_karatsuba w5_op.
 Instance w7_op : ZnZ.Ops (word w6 1) := mk_zn2z_ops_karatsuba w6_op.
 Instance w8_op : ZnZ.Ops (word w6 2) := mk_zn2z_ops_karatsuba w7_op.
 Instance w9_op : ZnZ.Ops (word w6 3) := mk_zn2z_ops_karatsuba w8_op.

 Section Make_op.
  Variable mk : forall (w':univ_of_cycles), ZnZ.Ops w' -> ZnZ.Ops (zn2z w').

  Fixpoint make_op_aux (n:nat) : ZnZ.Ops (word w6 (S n)):=
   match n return ZnZ.Ops (word w6 (S n)) with
   | O => w7_op
   | S n1 =>
     match n1 return ZnZ.Ops (word w6 (S (S n1))) with
     | O => w8_op
     | S n2 =>
       match n2 return ZnZ.Ops (word w6 (S (S (S n2)))) with
       | O => w9_op
       | S n3 => mk _ (mk _ (mk _ (make_op_aux n3)))
       end
     end
   end.

 End Make_op.

 Definition omake_op := make_op_aux mk_zn2z_ops_karatsuba.


 Definition make_op_list := dmemo_list _ omake_op.

 Instance make_op n : ZnZ.Ops (word w6 (S n))
  := dmemo_get _ omake_op n make_op_list.

 Ltac unfold_ops := unfold omake_op, make_op_aux, w9_op, w8_op.

 Lemma make_op_omake: forall n, make_op n = omake_op n.
 Proof.
 intros n; unfold make_op, make_op_list.
 refine (dmemo_get_correct _ _ _).
 Qed.

 Theorem make_op_S: forall n,
   make_op (S n) = mk_zn2z_ops_karatsuba (make_op n).
 Proof.
 intros n. do 2 rewrite make_op_omake.
 revert n. fix IHn 1.
 do 3 (destruct n; [unfold_ops; reflexivity|]).
 simpl mk_zn2z_ops_karatsuba. simpl word in *.
 rewrite <- (IHn n). auto.
 Qed.

 (** * The main type [t], isomorphic with [exists n, word w0 n] *)

 Inductive t' :=
  | N0 : w0 -> t'
  | N1 : w1 -> t'
  | N2 : w2 -> t'
  | N3 : w3 -> t'
  | N4 : w4 -> t'
  | N5 : w5 -> t'
  | N6 : w6 -> t'
  | Nn : forall n, word w6 (S n) -> t'.

 Definition t := t'.

 (** * A generic toolbox for building and deconstructing [t] *)

 Local Notation SizePlus n := (S (S (S (S (S (S n)))))).
 Local Notation Size := (SizePlus O).

 Tactic Notation (at level 3) "do_size" tactic3(t) := do 7 t.

 Definition dom_t n := match n with
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | 5 => w5
  | 6 => w6
  | SizePlus n => word w6 n
 end.

 Instance dom_op n : ZnZ.Ops (dom_t n) | 10.
 Proof.
  do_size (destruct n; [simpl;auto with *|]).
  unfold dom_t. auto with *.
 Defined.

 Definition iter_t {A:Type}(f : forall n, dom_t n -> A) : t -> A :=
  let f0 := f 0 in
  let f1 := f 1 in
  let f2 := f 2 in
  let f3 := f 3 in
  let f4 := f 4 in
  let f5 := f 5 in
  let f6 := f 6 in
  let fn n := f (SizePlus (S n)) in
  fun x => match x with
   | N0 wx => f0 wx
   | N1 wx => f1 wx
   | N2 wx => f2 wx
   | N3 wx => f3 wx
   | N4 wx => f4 wx
   | N5 wx => f5 wx
   | N6 wx => f6 wx
   | Nn n wx => fn n wx
  end.

 Definition mk_t (n:nat) : dom_t n -> t :=
  match n as n' return dom_t n' -> t with
   | 0 => N0
   | 1 => N1
   | 2 => N2
   | 3 => N3
   | 4 => N4
   | 5 => N5
   | 6 => N6
   | SizePlus (S n) => Nn n
  end.

 Definition level := iter_t (fun n _ => n).

 Inductive View_t : t -> Prop :=
  Mk_t : forall n (x : dom_t n), View_t (mk_t n x).

 Lemma destr_t : forall x, View_t x.
 Proof.
 intros x. generalize (Mk_t (level x)). destruct x; simpl; auto.
 Defined.

 Lemma iter_mk_t : forall A (f:forall n, dom_t n -> A),
 forall n x, iter_t f (mk_t n x) = f n x.
 Proof.
 do_size (destruct n; try reflexivity).
 Qed.

 (** * Projection to ZArith *)

 Definition to_Z : t -> Z :=
  Eval lazy beta iota delta [iter_t dom_t dom_op] in
  iter_t (fun _ x => ZnZ.to_Z x).

 Notation "[ x ]" := (to_Z x).

 Theorem spec_mk_t : forall n (x:dom_t n), [mk_t n x] = ZnZ.to_Z x.
 Proof.
 intros. change to_Z with (iter_t (fun _ x => ZnZ.to_Z x)).
 rewrite iter_mk_t; auto.
 Qed.

 (** * Regular make op, without memoization or karatsuba

     This will normally never be used for actual computations,
     but only for specification purpose when using
     [word (dom_t n) m] intermediate values. *)

 Fixpoint nmake_op (ww:univ_of_cycles) (ww_op: ZnZ.Ops ww) (n: nat) :
       ZnZ.Ops (word ww n) :=
  match n return ZnZ.Ops (word ww n) with
   O => ww_op
  | S n1 => mk_zn2z_ops (nmake_op ww ww_op n1)
  end.

 Definition eval n m := ZnZ.to_Z (Ops:=nmake_op _ (dom_op n) m).

 Theorem nmake_op_S: forall (ww:univ_of_cycles) (w_op: ZnZ.Ops ww) x,
   nmake_op _ w_op (S x) = mk_zn2z_ops (nmake_op _ w_op x).
 Proof.
 auto.
 Qed.

 Theorem digits_nmake_S :forall n (ww:univ_of_cycles) (w_op: ZnZ.Ops ww),
    ZnZ.digits (nmake_op _ w_op (S n)) =
    xO (ZnZ.digits (nmake_op _ w_op n)).
 Proof.
 auto.
 Qed.

 Theorem digits_nmake : forall n (ww:univ_of_cycles) (w_op: ZnZ.Ops ww),
    ZnZ.digits (nmake_op _ w_op n) = Pos.shiftl_nat (ZnZ.digits w_op) n.
 Proof.
 induction n. auto.
 intros ww ww_op. rewrite Pshiftl_nat_S, <- IHn; auto.
 Qed.

 Theorem nmake_double: forall n (ww:univ_of_cycles) (w_op: ZnZ.Ops ww),
    ZnZ.to_Z (Ops:=nmake_op _ w_op n) =
    @DoubleBase.double_to_Z _ (ZnZ.digits w_op) (ZnZ.to_Z (Ops:=w_op)) n.
 Proof.
 intros n; elim n; auto; clear n.
 intros n Hrec ww ww_op; simpl DoubleBase.double_to_Z; unfold zn2z_to_Z.
 rewrite <- Hrec; auto.
 unfold DoubleBase.double_wB; rewrite <- digits_nmake; auto.
 Qed.

 Theorem nmake_WW: forall (ww:univ_of_cycles) ww_op n xh xl,
  (ZnZ.to_Z (Ops:=nmake_op ww ww_op (S n)) (WW xh xl) =
   ZnZ.to_Z (Ops:=nmake_op ww ww_op n) xh *
    base (ZnZ.digits (nmake_op ww ww_op n)) +
   ZnZ.to_Z (Ops:=nmake_op ww ww_op n) xl)%Z.
 Proof.
 auto.
 Qed.

 (** * The specification proofs for the word operators *)

 Typeclasses Opaque w1 w2 w3 w4 w5 w6.

 Instance w0_spec: ZnZ.Specs w0_op := W0.specs.
 Instance w1_spec: ZnZ.Specs w1_op := mk_zn2z_specs w0_spec.
 Instance w2_spec: ZnZ.Specs w2_op := mk_zn2z_specs w1_spec.
 Instance w3_spec: ZnZ.Specs w3_op := mk_zn2z_specs w2_spec.
 Instance w4_spec: ZnZ.Specs w4_op := mk_zn2z_specs_karatsuba w3_spec.
 Instance w5_spec: ZnZ.Specs w5_op := mk_zn2z_specs_karatsuba w4_spec.
 Instance w6_spec: ZnZ.Specs w6_op := mk_zn2z_specs_karatsuba w5_spec.
 Instance w7_spec: ZnZ.Specs w7_op := mk_zn2z_specs_karatsuba w6_spec.

 Instance wn_spec (n:nat) : ZnZ.Specs (make_op n).
 Proof.
  induction n.
  rewrite make_op_omake; simpl; auto with *.
  rewrite make_op_S. exact (mk_zn2z_specs_karatsuba IHn).
 Qed.

 Instance dom_spec n : ZnZ.Specs (dom_op n) | 10.
 Proof.
  do_size (destruct n; auto with *). apply wn_spec.
 Qed.

 Let make_op_WW : forall n x y,
   (ZnZ.to_Z (Ops:=make_op (S n)) (WW x y) =
    ZnZ.to_Z (Ops:=make_op n) x * base (ZnZ.digits (make_op n))
     + ZnZ.to_Z (Ops:=make_op n) y)%Z.
 Proof.
 intros n x y; rewrite make_op_S; auto.
 Qed.

 (** * Zero *)

 Definition zero0 : w0 := ZnZ.zero.

 Definition zeron n : dom_t n :=
  match n with
   | O => zero0
   | SizePlus (S n) => W0
   | _ => W0
  end.

 Lemma spec_zeron : forall n, ZnZ.to_Z (zeron n) = 0%Z.
 Proof.
   do_size (destruct n;
            [match goal with
             |- @eq Z (_ (zeron ?n)) _ => 
               apply (ZnZ.spec_0 (Specs:=dom_spec n))
             end|]).
  destruct n; auto. simpl. rewrite make_op_S. fold word. 
  apply (ZnZ.spec_0 (Specs:=wn_spec (SizePlus 0))).
 Qed.

 (** * Digits *)

 Lemma digits_make_op_0 : forall n,
  ZnZ.digits (make_op n) = Pos.shiftl_nat (ZnZ.digits (dom_op Size)) (S n).
 Proof.
 induction n.
 auto.
 replace (ZnZ.digits (make_op (S n))) with (xO (ZnZ.digits (make_op n))).
  rewrite IHn; auto.
 rewrite make_op_S; auto.
 Qed.

 Lemma digits_make_op : forall n,
  ZnZ.digits (make_op n) = Pos.shiftl_nat (ZnZ.digits w0_op) (SizePlus (S n)).
 Proof.
 intros. rewrite digits_make_op_0.
 replace (SizePlus (S n)) with (S n + Size) by (rewrite <- plus_comm; auto).
 rewrite Pshiftl_nat_plus. auto.
 Qed.

 Lemma digits_dom_op : forall n,
  ZnZ.digits (dom_op n) = Pos.shiftl_nat (ZnZ.digits w0_op) n.
 Proof.
 do_size (destruct n; try reflexivity).
 exact (digits_make_op n).
 Qed.

 Lemma digits_dom_op_nmake : forall n m,
  ZnZ.digits (dom_op (m+n)) = ZnZ.digits (nmake_op _ (dom_op n) m).
 Proof.
 intros. rewrite digits_nmake, 2 digits_dom_op. apply Pshiftl_nat_plus.
 Qed.

 (** * Conversion between [zn2z (dom_t n)] and [dom_t (S n)].

     These two types are provably equal, but not convertible,
     hence we need some work. We now avoid using generic casts
     (i.e. rewrite via proof of equalities in types), since
     proving things with them is a mess.
 *)

 Definition succ_t n : zn2z (dom_t n) -> dom_t (S n) :=
  match n with
   | SizePlus (S _) => fun x => x
   | _ => fun x => x
  end.

 Lemma spec_succ_t : forall n x,
  ZnZ.to_Z (succ_t n x) =
  zn2z_to_Z (base (ZnZ.digits (dom_op n))) ZnZ.to_Z x.
 Proof.
 do_size (destruct n ; [reflexivity|]).
 intros. simpl. rewrite make_op_S. simpl. auto.
 Qed.

 Definition pred_t n : dom_t (S n) -> zn2z (dom_t n) :=
  match n with
   | SizePlus (S _) => fun x => x
   | _ => fun x => x
  end.

 Lemma succ_pred_t : forall n x, succ_t n (pred_t n x) = x.
 Proof.
 do_size (destruct n ; [reflexivity|]). reflexivity.
 Qed.

 (** We can hence project from [zn2z (dom_t n)] to [t] : *)

 Definition mk_t_S n (x : zn2z (dom_t n)) : t :=
  mk_t (S n) (succ_t n x).

 Lemma spec_mk_t_S : forall n x,
  [mk_t_S n x] = zn2z_to_Z (base (ZnZ.digits (dom_op n))) ZnZ.to_Z x.
 Proof.
 intros. unfold mk_t_S. rewrite spec_mk_t. apply spec_succ_t.
 Qed.

 Lemma mk_t_S_level : forall n x, level (mk_t_S n x) = S n.
 Proof.
 intros. unfold mk_t_S, level. rewrite iter_mk_t; auto.
 Qed.

 (** * Conversion from [word (dom_t n) m] to [dom_t (m+n)].

     Things are more complex here. We start with a naive version
     that breaks zn2z-trees and reconstruct them. Doing this is
     quite unfortunate, but I don't know how to fully avoid that.
     (cast someday ?). Then we build an optimized version where
     all basic cases (n<=6 or m<=7) are nicely handled.
 *)

 Definition zn2z_map {A} {B} (f:A->B) (x:zn2z A) : zn2z B :=
  match x with
   | W0 => W0
   | WW h l => WW (f h) (f l)
  end.

 Lemma zn2z_map_id : forall A f (x:zn2z A), (forall u, f u = u) ->
   zn2z_map f x = x.
 Proof.
  destruct x; auto; intros.
  simpl; f_equal; auto.
 Qed.

 (** The naive version *)

 Fixpoint plus_t n m : word (dom_t n) m -> dom_t (m+n) :=
  match m as m' return word (dom_t n) m' -> dom_t (m'+n) with
   | O => fun x => x
   | S m => fun x => succ_t _ (zn2z_map (plus_t n m) x)
  end.

 Theorem spec_plus_t : forall n m (x:word (dom_t n) m),
  ZnZ.to_Z (plus_t n m x) = eval n m x.
 Proof.
 unfold eval.
 induction m.
 simpl; auto.
 intros.
 simpl plus_t; simpl plus. rewrite spec_succ_t.
 destruct x.
 simpl; auto.
 fold word in w, w0.
 simpl. rewrite 2 IHm. f_equal. f_equal. f_equal.
 apply digits_dom_op_nmake.
 Qed.

 Definition mk_t_w n m (x:word (dom_t n) m) : t :=
   mk_t (m+n) (plus_t n m x).

 Theorem spec_mk_t_w : forall n m (x:word (dom_t n) m),
  [mk_t_w n m x] = eval n m x.
 Proof.
 intros. unfold mk_t_w. rewrite spec_mk_t. apply spec_plus_t.
 Qed.

 (** The optimized version.

     NB: the last particular case for m could depend on n,
     but it's simplier to just expand everywhere up to m=7
     (cf [mk_t_w'] later).
 *)

 Definition plus_t' n : forall m, word (dom_t n) m -> dom_t (m+n) :=
   match n return (forall m, word (dom_t n) m -> dom_t (m+n)) with
     | SizePlus (S n') as n => plus_t n
     | _ as n =>
         fun m => match m return (word (dom_t n) m -> dom_t (m+n)) with
                    | SizePlus (S (S m')) as m => plus_t n m
                    | _ => fun x => x
                  end
   end.

 Lemma plus_t_equiv : forall n m x,
  plus_t' n m x = plus_t n m x.
 Proof.
  (do_size try destruct n); try reflexivity;
   (do_size try destruct m); try destruct m; try reflexivity;
     simpl; symmetry; repeat (intros; apply zn2z_map_id; trivial).
 Qed.

 Lemma spec_plus_t' : forall n m x,
  ZnZ.to_Z (plus_t' n m x) = eval n m x.
 Proof.
 intros; rewrite plus_t_equiv. apply spec_plus_t.
 Qed.

 (** Particular cases [Nk x] = eval i j x with specific k,i,j
     can be solved by the following tactic *)

 Ltac solve_eval :=
  intros; rewrite <- spec_plus_t'; unfold to_Z; simpl dom_op; reflexivity.

 (** The last particular case that remains useful *)

 Lemma spec_eval_size : forall n x, [Nn n x] = eval Size (S n) x.
 Proof.
 induction n.
 solve_eval.
 destruct x as [ | xh xl ].
  simpl. unfold eval. rewrite make_op_S. rewrite nmake_op_S. auto.
 simpl word in xh, xl |- *.
 unfold to_Z in *. rewrite make_op_WW.
 unfold eval in *. rewrite nmake_WW.
 f_equal; auto.
 f_equal; auto.
 f_equal.
 rewrite <- digits_dom_op_nmake. rewrite plus_comm; auto.
 Qed.

 (** An optimized [mk_t_w].

     We could say mk_t_w' := mk_t _ (plus_t' n m x)
     (TODO: WHY NOT, BTW ??).
     Instead we directly define functions for all intersting [n],
     reverting to naive [mk_t_w] at places that should normally
     never be used (see [mul] and [div_gt]).
 *)

 Definition mk_t_0w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w0 (S m) -> t with
    | (S (S (S (S (S (S (S _))))))) as p => mk_t_w 0 (S p)
    | p => mk_t (1+p)
  end.

 Definition mk_t_1w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w1 (S m) -> t with
    | (S (S (S (S (S (S _)))))) as p => mk_t_w 1 (S p)
    | p => mk_t (2+p)
  end.

 Definition mk_t_2w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w2 (S m) -> t with
    | (S (S (S (S (S _))))) as p => mk_t_w 2 (S p)
    | p => mk_t (3+p)
  end.

 Definition mk_t_3w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w3 (S m) -> t with
    | (S (S (S (S _)))) as p => mk_t_w 3 (S p)
    | p => mk_t (4+p)
  end.

 Definition mk_t_4w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w4 (S m) -> t with
    | (S (S (S _))) as p => mk_t_w 4 (S p)
    | p => mk_t (5+p)
  end.

 Definition mk_t_5w m := Eval cbv beta zeta iota delta [ mk_t plus ] in
  match m return word w5 (S m) -> t with
    | (S (S _)) as p => mk_t_w 5 (S p)
    | p => mk_t (6+p)
  end.

 Definition mk_t_w' n : forall m, word (dom_t n) (S m) -> t :=
  match n return (forall m, word (dom_t n) (S m) -> t) with
    | 0 => mk_t_0w
    | 1 => mk_t_1w
    | 2 => mk_t_2w
    | 3 => mk_t_3w
    | 4 => mk_t_4w
    | 5 => mk_t_5w
    | Size => Nn
    | _ as n' => fun m => mk_t_w n' (S m)
  end.

 Ltac solve_spec_mk_t_w' :=
  rewrite <- spec_plus_t';
  match goal with _ : word (dom_t ?n) ?m |- _ => apply (spec_mk_t (n+m)) end.

 Theorem spec_mk_t_w' :
  forall n m x, [mk_t_w' n m x] = eval n (S m) x.
 Proof.
 intros.
 repeat (apply spec_mk_t_w || (destruct n;
  [repeat (apply spec_mk_t_w || (destruct m; [solve_spec_mk_t_w'|]))|])).
 apply spec_eval_size.
 Qed.

 (** * Extend : injecting [dom_t n] into [word (dom_t n) (S m)] *)

 Definition extend n m (x:dom_t n) : word (dom_t n) (S m) :=
  DoubleBase.extend_aux m (WW (zeron n) x).

 Lemma spec_extend : forall n m x,
  [mk_t n x] = eval n (S m) (extend n m x).
 Proof.
 intros. unfold eval, extend.
 rewrite spec_mk_t.
 assert (H : forall (x:dom_t n),
              (ZnZ.to_Z (zeron n) * base (ZnZ.digits (dom_op n)) + ZnZ.to_Z x =
              ZnZ.to_Z x)%Z).
  clear; intros; rewrite spec_zeron; auto.
 rewrite <- (@DoubleBase.spec_extend _
              (WW (zeron n)) (ZnZ.digits (dom_op n)) ZnZ.to_Z H m x).
 simpl. rewrite digits_nmake, <- nmake_double. auto.
 Qed.

 (** A particular case of extend, used in [same_level]:
     [extend_size] is [extend Size] *)

 Definition extend_size := DoubleBase.extend (WW (W0:dom_t Size)).

 Lemma spec_extend_size : forall n x, [mk_t Size x] = [Nn n (extend_size n x)].
 Proof.
 intros. rewrite spec_eval_size. apply (spec_extend Size n).
 Qed.

 (** Misc results about extensions *)

 Let spec_extend_WW : forall n x,
  [Nn (S n) (WW W0 x)] = [Nn n x].
 Proof.
 intros n x.
 set (N:=SizePlus (S n)).
 change ([Nn (S n) (extend N 0 x)]=[mk_t N x]).
 rewrite (spec_extend N 0).
 solve_eval.
 Qed.

 Let spec_extend_tr: forall m n w,
 [Nn (m + n) (extend_tr w m)] = [Nn n w].
 Proof.
 induction m; auto.
 intros n x; simpl extend_tr.
 simpl plus; rewrite spec_extend_WW; auto.
 Qed.

 Let spec_cast_l: forall n m x1,
 [Nn n x1] =
 [Nn (Max.max n m) (castm (diff_r n m) (extend_tr x1 (snd (diff n m))))].
 Proof.
 intros n m x1; case (diff_r n m); simpl castm.
 rewrite spec_extend_tr; auto.
 Qed.

 Let spec_cast_r: forall n m x1,
 [Nn m x1] =
 [Nn (Max.max n m) (castm (diff_l n m) (extend_tr x1 (fst (diff n m))))].
 Proof.
 intros n m x1; case (diff_l n m); simpl castm.
 rewrite spec_extend_tr; auto.
 Qed.

 Ltac unfold_lets :=
  match goal with
   | h : _ |- _ => unfold h; clear h; unfold_lets
   | _ => idtac
  end.

 (** * [same_level]

     Generic binary operator construction, by extending the smaller
     argument to the level of the other.
 *)

 Section SameLevel.

  Variable res: Type.
  Variable P : Z -> Z -> res -> Prop.
  Variable f : forall n, dom_t n -> dom_t n -> res.
  Variable Pf : forall n x y, P (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y).

  Let f0 : w0 -> w0 -> res := f 0.
  Let f1 : w1 -> w1 -> res := f 1.
  Let f2 : w2 -> w2 -> res := f 2.
  Let f3 : w3 -> w3 -> res := f 3.
  Let f4 : w4 -> w4 -> res := f 4.
  Let f5 : w5 -> w5 -> res := f 5.
  Let f6 : w6 -> w6 -> res := f 6.
  Let fn n := f (SizePlus (S n)).

  Let Pf' :
   forall n x y u v, u = [mk_t n x] -> v = [mk_t n y] -> P u v (f n x y).
  Proof.
  intros. subst. rewrite 2 spec_mk_t. apply Pf.
  Qed.

  Notation same_level_folded := (fun x y => match x, y with
  | N0 wx, N0 wy => f0 wx wy
  | N0 wx, N1 wy => f1 (extend 0 0 wx) wy
  | N0 wx, N2 wy => f2 (extend 0 1 wx) wy
  | N0 wx, N3 wy => f3 (extend 0 2 wx) wy
  | N0 wx, N4 wy => f4 (extend 0 3 wx) wy
  | N0 wx, N5 wy => f5 (extend 0 4 wx) wy
  | N0 wx, N6 wy => f6 (extend 0 5 wx) wy
  | N0 wx, Nn m wy => fn m (extend_size m (extend 0 5 wx)) wy
  | N1 wx, N0 wy => f1 wx (extend 0 0 wy)
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f2 (extend 1 0 wx) wy
  | N1 wx, N3 wy => f3 (extend 1 1 wx) wy
  | N1 wx, N4 wy => f4 (extend 1 2 wx) wy
  | N1 wx, N5 wy => f5 (extend 1 3 wx) wy
  | N1 wx, N6 wy => f6 (extend 1 4 wx) wy
  | N1 wx, Nn m wy => fn m (extend_size m (extend 1 4 wx)) wy
  | N2 wx, N0 wy => f2 wx (extend 0 1 wy)
  | N2 wx, N1 wy => f2 wx (extend 1 0 wy)
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f3 (extend 2 0 wx) wy
  | N2 wx, N4 wy => f4 (extend 2 1 wx) wy
  | N2 wx, N5 wy => f5 (extend 2 2 wx) wy
  | N2 wx, N6 wy => f6 (extend 2 3 wx) wy
  | N2 wx, Nn m wy => fn m (extend_size m (extend 2 3 wx)) wy
  | N3 wx, N0 wy => f3 wx (extend 0 2 wy)
  | N3 wx, N1 wy => f3 wx (extend 1 1 wy)
  | N3 wx, N2 wy => f3 wx (extend 2 0 wy)
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f4 (extend 3 0 wx) wy
  | N3 wx, N5 wy => f5 (extend 3 1 wx) wy
  | N3 wx, N6 wy => f6 (extend 3 2 wx) wy
  | N3 wx, Nn m wy => fn m (extend_size m (extend 3 2 wx)) wy
  | N4 wx, N0 wy => f4 wx (extend 0 3 wy)
  | N4 wx, N1 wy => f4 wx (extend 1 2 wy)
  | N4 wx, N2 wy => f4 wx (extend 2 1 wy)
  | N4 wx, N3 wy => f4 wx (extend 3 0 wy)
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f5 (extend 4 0 wx) wy
  | N4 wx, N6 wy => f6 (extend 4 1 wx) wy
  | N4 wx, Nn m wy => fn m (extend_size m (extend 4 1 wx)) wy
  | N5 wx, N0 wy => f5 wx (extend 0 4 wy)
  | N5 wx, N1 wy => f5 wx (extend 1 3 wy)
  | N5 wx, N2 wy => f5 wx (extend 2 2 wy)
  | N5 wx, N3 wy => f5 wx (extend 3 1 wy)
  | N5 wx, N4 wy => f5 wx (extend 4 0 wy)
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f6 (extend 5 0 wx) wy
  | N5 wx, Nn m wy => fn m (extend_size m (extend 5 0 wx)) wy
  | N6 wx, N0 wy => f6 wx (extend 0 5 wy)
  | N6 wx, N1 wy => f6 wx (extend 1 4 wy)
  | N6 wx, N2 wy => f6 wx (extend 2 3 wy)
  | N6 wx, N3 wy => f6 wx (extend 3 2 wy)
  | N6 wx, N4 wy => f6 wx (extend 4 1 wy)
  | N6 wx, N5 wy => f6 wx (extend 5 0 wy)
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, Nn m wy => fn m (extend_size m wx) wy
  | Nn n wx, N0 wy => fn n wx (extend_size n (extend 0 5 wy))
  | Nn n wx, N1 wy => fn n wx (extend_size n (extend 1 4 wy))
  | Nn n wx, N2 wy => fn n wx (extend_size n (extend 2 3 wy))
  | Nn n wx, N3 wy => fn n wx (extend_size n (extend 3 2 wy))
  | Nn n wx, N4 wy => fn n wx (extend_size n (extend 4 1 wy))
  | Nn n wx, N5 wy => fn n wx (extend_size n (extend 5 0 wy))
  | Nn n wx, N6 wy => fn n wx (extend_size n wy)
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     fn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end).

  Definition same_level := Eval lazy beta iota delta
   [ DoubleBase.extend DoubleBase.extend_aux extend zeron ]
  in same_level_folded.

  Lemma spec_same_level_0: forall x y, P [x] [y] (same_level x y).
  Proof.
  change same_level with same_level_folded. unfold_lets.
  destruct x, y; apply Pf'; simpl mk_t; rewrite <- ?spec_extend_size;
  match goal with
   | |- context [ extend ?n ?m _ ] => apply (spec_extend n m)
   | |- context [ castm _ _ ] => apply spec_cast_l || apply spec_cast_r
   | _ => reflexivity
  end.
  Qed.

 End SameLevel.

 Arguments same_level [res] f x y.

 Theorem spec_same_level_dep :
  forall res
   (P : nat -> Z -> Z -> res -> Prop)
   (Pantimon : forall n m z z' r, n <= m -> P m z z' r -> P n z z' r)
   (f : forall n, dom_t n -> dom_t n -> res)
   (Pf: forall n x y, P n (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y)),
   forall x y, P (level x) [x] [y] (same_level f x y).
 Proof.
 intros res P Pantimon f Pf.
 set (f' := fun n x y => (n, f n x y)).
 set (P' := fun z z' r => P (fst r) z z' (snd r)).
 assert (FST : forall x y, level x <= fst (same_level f' x y))
  by (destruct x, y; simpl; lia).
 assert (SND : forall x y, same_level f x y = snd (same_level f' x y))
  by (destruct x, y; reflexivity).
 intros. eapply Pantimon; [eapply FST|].
 rewrite SND. eapply (@spec_same_level_0 _ P' f'); eauto.
 Qed.

 (** * [iter]

     Generic binary operator construction, by splitting the larger
     argument in blocks and applying the smaller argument to them.
 *)

 Section Iter.

  Variable res: Type.
  Variable P: Z -> Z -> res -> Prop.

  Variable f : forall n, dom_t n -> dom_t n -> res.
  Variable Pf : forall n x y, P (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y).

  Variable fd : forall n m, dom_t n -> word (dom_t n) (S m) -> res.
  Variable fg : forall n m, word (dom_t n) (S m) -> dom_t n -> res.
  Variable Pfd : forall n m x y, P (ZnZ.to_Z x) (eval n (S m) y) (fd n m x y).
  Variable Pfg : forall n m x y, P (eval n (S m) x) (ZnZ.to_Z y) (fg n m x y).

  Variable fnm: forall n m, word (dom_t Size) (S n) -> word (dom_t Size) (S m) -> res.
  Variable Pfnm: forall n m x y, P [Nn n x] [Nn m y] (fnm n m x y).

  Let Pf' :
   forall n x y u v, u = [mk_t n x] -> v = [mk_t n y] -> P u v (f n x y).
  Proof.
  intros. subst. rewrite 2 spec_mk_t. apply Pf.
  Qed.

  Let Pfd' : forall n m x y u v, u = [mk_t n x] -> v = eval n (S m) y ->
   P u v (fd n m x y).
  Proof.
  intros. subst. rewrite spec_mk_t. apply Pfd.
  Qed.

  Let Pfg' : forall n m x y u v, u = eval n (S m) x -> v = [mk_t n y] ->
   P u v (fg n m x y).
  Proof.
  intros. subst. rewrite spec_mk_t. apply Pfg.
  Qed.

  Let f0 := f 0.
  Let f1 := f 1.
  Let f2 := f 2.
  Let f3 := f 3.
  Let f4 := f 4.
  Let f5 := f 5.
  Let f6 := f 6.
  Let f0n := fd 0.
  Let fn0 := fg 0.
  Let f1n := fd 1.
  Let fn1 := fg 1.
  Let f2n := fd 2.
  Let fn2 := fg 2.
  Let f3n := fd 3.
  Let fn3 := fg 3.
  Let f4n := fd 4.
  Let fn4 := fg 4.
  Let f5n := fd 5.
  Let fn5 := fg 5.
  Let f6n := fd 6.
  Let fn6 := fg 6.
  Notation iter_folded := (fun x y => match x, y with
  | N0 wx, N0 wy => f0 wx wy
  | N0 wx, N1 wy => f0n 0 wx wy
  | N0 wx, N2 wy => f0n 1 wx wy
  | N0 wx, N3 wy => f0n 2 wx wy
  | N0 wx, N4 wy => f0n 3 wx wy
  | N0 wx, N5 wy => f0n 4 wx wy
  | N0 wx, N6 wy => f0n 5 wx wy
  | N0 wx, Nn m wy => f6n m (extend 0 5 wx) wy
  | N1 wx, N0 wy => fn0 0 wx wy
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f1n 0 wx wy
  | N1 wx, N3 wy => f1n 1 wx wy
  | N1 wx, N4 wy => f1n 2 wx wy
  | N1 wx, N5 wy => f1n 3 wx wy
  | N1 wx, N6 wy => f1n 4 wx wy
  | N1 wx, Nn m wy => f6n m (extend 1 4 wx) wy
  | N2 wx, N0 wy => fn0 1 wx wy
  | N2 wx, N1 wy => fn1 0 wx wy
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f2n 0 wx wy
  | N2 wx, N4 wy => f2n 1 wx wy
  | N2 wx, N5 wy => f2n 2 wx wy
  | N2 wx, N6 wy => f2n 3 wx wy
  | N2 wx, Nn m wy => f6n m (extend 2 3 wx) wy
  | N3 wx, N0 wy => fn0 2 wx wy
  | N3 wx, N1 wy => fn1 1 wx wy
  | N3 wx, N2 wy => fn2 0 wx wy
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f3n 0 wx wy
  | N3 wx, N5 wy => f3n 1 wx wy
  | N3 wx, N6 wy => f3n 2 wx wy
  | N3 wx, Nn m wy => f6n m (extend 3 2 wx) wy
  | N4 wx, N0 wy => fn0 3 wx wy
  | N4 wx, N1 wy => fn1 2 wx wy
  | N4 wx, N2 wy => fn2 1 wx wy
  | N4 wx, N3 wy => fn3 0 wx wy
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f4n 0 wx wy
  | N4 wx, N6 wy => f4n 1 wx wy
  | N4 wx, Nn m wy => f6n m (extend 4 1 wx) wy
  | N5 wx, N0 wy => fn0 4 wx wy
  | N5 wx, N1 wy => fn1 3 wx wy
  | N5 wx, N2 wy => fn2 2 wx wy
  | N5 wx, N3 wy => fn3 1 wx wy
  | N5 wx, N4 wy => fn4 0 wx wy
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f5n 0 wx wy
  | N5 wx, Nn m wy => f6n m (extend 5 0 wx) wy
  | N6 wx, N0 wy => fn0 5 wx wy
  | N6 wx, N1 wy => fn1 4 wx wy
  | N6 wx, N2 wy => fn2 3 wx wy
  | N6 wx, N3 wy => fn3 2 wx wy
  | N6 wx, N4 wy => fn4 1 wx wy
  | N6 wx, N5 wy => fn5 0 wx wy
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, Nn m wy => f6n m wx wy
  | Nn n wx, N0 wy => fn6 n wx (extend 0 5 wy)
  | Nn n wx, N1 wy => fn6 n wx (extend 1 4 wy)
  | Nn n wx, N2 wy => fn6 n wx (extend 2 3 wy)
  | Nn n wx, N3 wy => fn6 n wx (extend 3 2 wy)
  | Nn n wx, N4 wy => fn6 n wx (extend 4 1 wy)
  | Nn n wx, N5 wy => fn6 n wx (extend 5 0 wy)
  | Nn n wx, N6 wy => fn6 n wx wy
  | Nn n wx, Nn m wy => fnm n m wx wy
  end).

  Definition iter := Eval lazy beta iota delta
   [extend DoubleBase.extend DoubleBase.extend_aux zeron]
   in iter_folded.

  Lemma spec_iter: forall x y, P [x] [y] (iter x y).
  Proof.
  change iter with iter_folded; unfold_lets.
  destruct x; destruct y; apply Pf' || apply Pfd' || apply Pfg' || apply Pfnm;
  simpl mk_t;
  match goal with
   | |- ?x = ?x => reflexivity
   | |- [Nn _ _] = _ => apply spec_eval_size
   | |- context [extend ?n ?m _] => apply (spec_extend n m)
   | _ => idtac
  end;
  unfold to_Z; rewrite <- spec_plus_t'; simpl dom_op; reflexivity.
  Qed.

  End Iter.

  Definition switch
  (P:nat->Type)(f0:P 0)(f1:P 1)(f2:P 2)(f3:P 3)(f4:P 4)(f5:P 5)(f6:P 6)
  (fn:forall n, P n) n :=
  match n return P n with
   | 0 => f0
   | 1 => f1
   | 2 => f2
   | 3 => f3
   | 4 => f4
   | 5 => f5
   | 6 => f6
   | n => fn n
  end.

  Lemma spec_switch : forall P (f:forall n, P n) n,
   switch P (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) f n = f n.
  Proof.
  repeat (destruct n; try reflexivity).
  Qed.

  (** * [iter_sym]

    A variant of [iter] for symmetric functions, or pseudo-symmetric
    functions (when f y x can be deduced from f x y).
  *)

  Section IterSym.

  Variable res: Type.
  Variable P: Z -> Z -> res -> Prop.

  Variable f : forall n, dom_t n -> dom_t n -> res.
  Variable Pf : forall n x y, P (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y).

  Variable fg : forall n m, word (dom_t n) (S m) -> dom_t n -> res.
  Variable Pfg : forall n m x y, P (eval n (S m) x) (ZnZ.to_Z y) (fg n m x y).

  Variable fnm: forall n m, word (dom_t Size) (S n) -> word (dom_t Size) (S m) -> res.
  Variable Pfnm: forall n m x y, P [Nn n x] [Nn m y] (fnm n m x y).

  Variable opp: res -> res.
  Variable Popp : forall u v r, P u v r -> P v u (opp r).

  Let f0 := f 0.
  Let f1 := f 1.
  Let f2 := f 2.
  Let f3 := f 3.
  Let f4 := f 4.
  Let f5 := f 5.
  Let f6 := f 6.
  Let fn0 := fg 0.
  Let fn1 := fg 1.
  Let fn2 := fg 2.
  Let fn3 := fg 3.
  Let fn4 := fg 4.
  Let fn5 := fg 5.
  Let fn6 := fg 6.
  Let f' := switch _ f0 f1 f2 f3 f4 f5 f6 f.
  Let fg' := switch _ fn0 fn1 fn2 fn3 fn4 fn5 fn6 fg.
  Local Notation iter_sym_folded :=
   (iter res f' (fun n m x y => opp (fg' n m y x)) fg' fnm).

  Definition iter_sym :=
   Eval lazy beta zeta iota delta [iter f' fg' switch] in iter_sym_folded.

  Lemma spec_iter_sym: forall x y, P [x] [y] (iter_sym x y).
  Proof.
  intros. change iter_sym with iter_sym_folded. apply spec_iter; clear x y.
  unfold_lets.
  intros. rewrite spec_switch. auto.
  intros. apply Popp. unfold_lets. rewrite spec_switch; auto.
  intros. unfold_lets. rewrite spec_switch; auto.
  auto.
  Qed.

  End IterSym.

 (** * Reduction

     [reduce] can be used instead of [mk_t], it will choose the
     lowest possible level. NB: We only search and remove leftmost
     W0's via ZnZ.eq0, any non-W0 block ends the process, even
     if its value is 0.
 *)

 (** First, a direct version ... *)

 Fixpoint red_t n : dom_t n -> t :=
  match n return dom_t n -> t with
   | O => N0
   | S n => fun x =>
     let x' := pred_t n x in
     reduce_n1 _ _ (N0 zero0) ZnZ.eq0 (red_t n) (mk_t_S n) x'
  end.

 Lemma spec_red_t : forall n x, [red_t n x] = [mk_t n x].
 Proof.
 induction n.
 reflexivity.
 intros.
 simpl red_t. unfold reduce_n1.
 rewrite <- (succ_pred_t n x) at 2.
 remember (pred_t n x) as x'.
 rewrite spec_mk_t, spec_succ_t.
 destruct x' as [ | xh xl]. simpl. apply ZnZ.spec_0.
 generalize (ZnZ.spec_eq0 xh); case ZnZ.eq0; intros H.
 rewrite IHn, spec_mk_t. simpl. rewrite H; auto.
 apply spec_mk_t_S.
 Qed.

 (** ... then a specialized one *)

 Definition eq00 := @ZnZ.eq0 _ w0_op.
 Definition eq01 := @ZnZ.eq0 _ w1_op.
 Definition eq02 := @ZnZ.eq0 _ w2_op.
 Definition eq03 := @ZnZ.eq0 _ w3_op.
 Definition eq04 := @ZnZ.eq0 _ w4_op.
 Definition eq05 := @ZnZ.eq0 _ w5_op.
 Definition eq06 := @ZnZ.eq0 _ w6_op.

 Definition reduce_0 := N0.
 Definition reduce_1 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq00 reduce_0 N1.
 Definition reduce_2 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq01 reduce_1 N2.
 Definition reduce_3 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq02 reduce_2 N3.
 Definition reduce_4 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq03 reduce_3 N4.
 Definition reduce_5 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq04 reduce_4 N5.
 Definition reduce_6 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq05 reduce_5 N6.
 Definition reduce_7 :=
  Eval lazy beta iota delta [reduce_n1] in
   reduce_n1 _ _ (N0 zero0) eq06 reduce_6 (Nn 0).
 Definition reduce_n n :=
  Eval lazy beta iota delta [reduce_n] in
   reduce_n _ _ (N0 zero0) reduce_7 Nn n.

 Definition reduce n : dom_t n -> t :=
  match n with
   | 0 => reduce_0
   | 1 => reduce_1
   | 2 => reduce_2
   | 3 => reduce_3
   | 4 => reduce_4
   | 5 => reduce_5
   | 6 => reduce_6
   | SizePlus (S n) => reduce_n n
  end.

 Ltac unfold_red := unfold reduce, reduce_1, reduce_2, reduce_3, reduce_4, reduce_5, reduce_6.

 Declare Equivalent Keys reduce reduce_0.
 Declare Equivalent Keys reduce reduce_1.
 Declare Equivalent Keys reduce reduce_2.
 Declare Equivalent Keys reduce reduce_3.
 Declare Equivalent Keys reduce reduce_4.
 Declare Equivalent Keys reduce reduce_5.
 Declare Equivalent Keys reduce reduce_6.
 Declare Equivalent Keys reduce_n reduce_7.

 Ltac solve_red :=
 let H := fresh in let G := fresh in
 match goal with
  | |- ?P (S ?n) => assert (H:P n) by solve_red
  | _ => idtac
 end;
 intros n G x; destruct (le_lt_eq_dec _ _ G) as [LT|EQ];
 solve [
  apply (H _ (lt_n_Sm_le _ _ LT)) |
  inversion LT |
  subst; change (reduce 0 x = red_t 0 x); reflexivity |
  specialize (H (pred n)); subst; destruct x;
   [|unfold_red; rewrite H; auto]; reflexivity
 ].

 Lemma reduce_equiv : forall n x, n <= Size -> reduce n x = red_t n x.
 Proof.
 set (P N := forall n, n <= N -> forall x, reduce n x = red_t n x).
 intros n x H. revert n H x. change (P Size). solve_red.
 Qed.

 Lemma spec_reduce_n : forall n x, [reduce_n n x] = [Nn n x].
 Proof.
 assert (H : forall x, reduce_7 x = red_t (SizePlus 1) x).
  destruct x; [|unfold reduce_7; rewrite (reduce_equiv Size)]; auto.
 induction n.
   intros. rewrite H. apply spec_red_t.
 destruct x as [|xh xl].
 simpl. rewrite make_op_S. exact ZnZ.spec_0.
 fold word in *.
 destruct xh; auto.
 simpl reduce_n.
 rewrite IHn.
 rewrite spec_extend_WW; auto.
 Qed.

 Lemma spec_reduce : forall n x, [reduce n x] = ZnZ.to_Z x.
 Proof.
 do_size (destruct n;
       [intros; rewrite reduce_equiv;[apply spec_red_t|auto with arith]|]).
 apply spec_reduce_n.
 Qed.

End Make.

