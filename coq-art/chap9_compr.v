Require Export ZArith.

Require Export List.

Require Export Arith.

Require Export Lia.

Require Export Zwf.

Require Import depend.

Require Import RelationClasses.

Import Relations.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0%nat
  | S p => S (S (mult2 p))
  end.

Parameter prime : nat->Prop.

Section div_pair_section.

Open Scope Z_scope.

Variable div_pair :
    forall a b:Z, 0 < b ->
                       {p:Z*Z | a = fst p * b + snd p /\ 0 <= snd p < b}.

Definition div_pair' (a:Z)(x:{b:Z | 0 < b}) : Z*Z :=
   match x with
   | exist _ b h => let (v, _) := div_pair a b h in v
   end.

End div_pair_section.

Section div2_of_even_section.

Open Scope nat_scope.

Variable even : nat->Prop.

Variables (div2_of_even : forall n:nat, even n -> {p:nat | n = p+p})
           (test_even : forall n:nat, {even n}+{even (pred n)} ).

Definition div2_gen (n:nat) :
   {p:nat | n = p+p}+{p:nat | pred n = p+p} :=
   match test_even n with
   | left h => inl _ (div2_of_even n h)
   | right h' => inr _ (div2_of_even (pred n) h')
   end.

End div2_of_even_section.

Definition eq_dec (A:Type) := forall x y:A, {x = y}+{x <> y}.

Definition pred' (n:nat) : {p:nat | n = S p}+{n = 0} :=
  match n return {p:nat | n = S p}+{n = 0} with
  | O => inright _ (refl_equal 0)
  | S p =>
     inleft _
       (exist (fun p':nat => S p = S p') p (refl_equal (S p)))
  end.

Check ({p:nat | 0 = S p }+{0 = 0}).

Check (fun p:nat =>{p':nat | S p = S p'}+{S p = 0}).

Ltac custom_tac11 H0 := elim H0; simpl; auto.

Ltac custom_tac3 H0 := apply H0; assumption.

Ltac custom_tac18 H0 := auto; apply H0; auto.

Ltac custom_tac4 H0 H1 := intros H0 H1; elim H1.

Ltac custom_tac16 H0 H1 := rewrite H0; rewrite H1.

Ltac custom_tac6  := intros; discriminate.

Ltac custom_tac13 H0 := intro; subst H0.

Ltac custom_tac14  := split; try discriminate.

Definition pred'' : forall n:nat, {p:nat | n = S p}+{n = 0}.
Proof. intros n; case n. right; apply refl_equal. intros p; left; exists p; reflexivity. Defined.

Definition pred_partial : forall n:nat, n <> 0 -> nat.
Proof. intros n; case n. intros h; elim h; reflexivity. intros p h'; exact p. Defined.

Theorem le_2_n_not_zero : forall n:nat, 2 <= n -> n <> 0.
Proof. intros n Hle; elim Hle; intros; discriminate. Qed.

Theorem le_2_n_pred' :
 forall n:nat, 2 <= n -> forall h:n <> 0, pred_partial n h <> 0.
Proof. intros n Hle; elim Hle. intros; discriminate. simpl; intros; apply le_2_n_not_zero; assumption. Qed.

Theorem le_2_n_pred :
 forall (n:nat)(h:2 <= n), pred_partial n (le_2_n_not_zero n h) <> 0.
Proof. intros n h; exact (le_2_n_pred' n h (le_2_n_not_zero n h)). Qed.

Definition pred_partial_2 (n:nat)(h:2 <= n) : nat :=
  pred_partial (pred_partial n (le_2_n_not_zero n h))
               (le_2_n_pred n h).

Check(forall n:nat, n <> 0 -> {v:nat | n = S v}).

Check (forall n:nat, 2 <= n -> {v:nat | n = S (S v)}).

Definition pred_strong : forall n:nat, n <> 0 -> {v:nat | n = S v}.
Proof. intros n; case n. - intros H; elim H. trivial. - intros p H'; exists p. trivial. Defined.

Theorem pred_strong2_th1 :
 forall n p:nat, 2 <= n -> n = S p -> p <> 0.
Proof. intros; lia. Qed.

Theorem pred_th1 : forall n p q:nat, n = S p -> p = S q -> n = S (S q).
Proof. intros; subst n; auto. Qed.

Definition pred_strong2 (n:nat)(h:2<=n):{v:nat | n = S (S v)} :=
  match pred_strong n (le_2_n_not_zero n h) with
  | exist _ p h' =>
      match pred_strong p (pred_strong2_th1 n p h h') with
      | exist _ p' h'' =>
          exist (fun x:nat => n = S (S x))
                p' (pred_th1 n p p' h' h'')
      end
  end.

Definition pred_strong2' :
  forall n:nat, 2 <= n -> {v:nat | n = S (S v)}.
Proof. intros n h; case (pred_strong n). - apply le_2_n_not_zero; assumption. - intros p h'; case (pred_strong p). + apply (pred_strong2_th1 n); assumption. + intros p' h''; exists p'; eapply pred_th1; eauto. Defined.

Section minimal_specification_strengthening.

Variable prime : nat->Prop.

Definition divides (n p:nat) : Prop := exists q:_, q*p = n.

Definition prime_divisor (n p:nat):= prime p /\ divides p n.

Variable prime_test : nat->bool.

Hypotheses
   (prime_test_t : forall n:nat, prime_test n = true -> prime n)
   (prime_test_f : forall n:nat, prime_test n = false -> ~prime n).

Variable get_primediv_weak : forall n:nat, ~prime n -> nat.

Hypothesis get_primediv_weak_ok :
     forall (n:nat)(H:~prime n), 1 < n ->
        prime_divisor n (get_primediv_weak n H).

Lemma divides_refl : forall n:nat, divides n n.
Proof. intro n; exists 1; simpl; auto. Qed.

#[local] Hint Resolve divides_refl : core.

Check (fun E:nat=>  fun n:nat => if prime_test n then n else E).

Definition bad_get_prime : nat->nat.
Proof. intro n; case_eq (prime_test n). - intro; exact n. - intro Hfalse; apply (get_primediv_weak n); auto. Defined.

Print bad_get_prime.

Definition stronger_prime_test :
   forall n:nat, {(prime_test n)=true}+{(prime_test n)=false}.
Proof. intro n; case (prime_test n). - left. reflexivity. - right. reflexivity. Defined.

Definition get_prime (n:nat) : nat :=
  match stronger_prime_test n with
  | left H => n
  | right H => get_primediv_weak n (prime_test_f n H)
  end.

Theorem get_primediv_ok :
  forall n:nat, 1 < n -> prime_divisor n (get_prime n).
Proof. intros n H; unfold get_prime. case (stronger_prime_test n); auto. split; auto. Qed.

End minimal_specification_strengthening.

Definition pred_partial' : forall n:nat, n <> 0 -> nat.
Proof. refine ( fun n => match n as x return x <> 0 -> nat with | O => fun h:0 <> 0 => _ | S p => fun h:S p <> 0 => p end). elim h; trivial. Defined.

Definition pred_partial_2' : forall n:nat, le 2 n -> nat.
Proof. refine ( fun n h=>(fun h':n<>0 => pred_partial (pred_partial n h') _) _). - apply le_2_n_pred'; auto. - apply le_2_n_not_zero; auto. Defined.

Definition pred_strong2'' : forall n:nat, 2<=n -> {v:nat | n = S (S v)}.
Proof. refine ( fun n h => match pred_strong n _ with | exist _ p h' => match pred_strong p _ with exist _ p' h'' => exist _ p' _ end end). - apply le_2_n_not_zero; assumption. - eapply pred_strong2_th1; eauto. - rewrite <- h''; trivial. Qed.

Require Import Program.

Fixpoint div2 (n:nat) : nat :=
  match n with 0 => 0 | 1 => 0 | S (S p) => S (div2 p) end.

Theorem div2_rect (P: nat -> Type) :
 P 0 -> P 1 ->
 (forall n, P n -> P (S n) -> P(S (S n)))->
 forall n:nat, P n.
Proof. intros H0 H1 H n; assert (X: ( P n * P (S n))%type). - induction n; intuition. - now destruct X. Defined.

Theorem div2_le : forall n:nat, div2 n <= n.
Proof. intro n; induction n using div2_rect; simpl; auto with arith. Qed.

Lemma double_div2_le : forall x:nat, div2 x + div2 x <= x.
Proof. intro n; induction n using div2_rect; simpl; auto with arith. lia. Qed.

Fixpoint div2'_aux (n:nat) : nat*nat :=
  match n with
  | 0 => (0, 0)
  | S p => let (v1,v2) := div2'_aux p in (v2, S v1)
  end.

Definition div2' (n:nat) : nat := fst (div2'_aux n).

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with O => n | S p => S (plus' n p)
  end.

Theorem plus'_O_n : forall n:nat, n=(plus' O n).
Proof. intros n; elim n; simpl; auto. Qed.

Theorem plus'_Sn_m : forall n m:nat, S (plus' n m) = plus' (S n) m.
Proof. intros n m; elim m; simpl; auto. Qed.

Theorem plus'_comm : forall n m:nat, plus' n m = plus' m n.
Proof. intros n m; elim m; simpl. - apply plus'_O_n. - intros p Hrec; rewrite <- plus'_Sn_m; auto. Qed.

Theorem plus_plus' : forall n m:nat, n+m = plus' n m.
Proof. intros n m; rewrite plus'_comm; elim n; simpl; auto. Qed.

Fixpoint plus'' (n m:nat){struct m} : nat :=
  match m with 0 => n | S p => plus'' (S n) p end.

Theorem plus''_Sn_m : forall n m:nat, S (plus'' n m) = plus'' (S n) m.
Proof. intros n m; generalize n; elim m; simpl. - auto. - now intros p Hrec n0. Qed.

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

Theorem rem_1_1_interval : 0 <= 0 < 1.
Proof. split; lia. Qed.

Theorem rem_1_even_interval : forall m:positive,  0 <= 1 < Zpos (xO m).
Proof. intros n'; split. - auto with zarith. - reflexivity. Qed.

Theorem rem_1_odd_interval : forall m:positive, 0 <= 1 < Zpos (xI m).
Proof. split. - auto with zarith. - compute; auto. Qed.

Theorem rem_even_ge_interval :
 forall m r:Z, 0 <= r < m ->  2*r >= m -> 0 <= 2*r - m < m.
Proof. intros; lia. Qed.

Theorem rem_even_lt_interval :
 forall m r:Z, 0 <= r < m -> 2*r < m -> 0 <= 2*r < m.
Proof. intros; lia. Qed.

Theorem rem_odd_ge_interval :
 forall m r:Z, 0 <= r < m -> 2*r + 1 >= m -> 2*r + 1 - m <  m.
Proof. intros; lia. Qed.

Theorem rem_odd_lt_interval :
 forall m r:Z, 0 <= r < m -> 2*r + 1 < m -> 0 <= 2*r + 1 < m.
Proof. intros; lia. Qed.

#[local] Hint Resolve rem_odd_ge_interval rem_even_ge_interval
 rem_odd_lt_interval rem_even_lt_interval rem_1_odd_interval
 rem_1_even_interval rem_1_1_interval : core.

Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
   [intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r' + 1)(Zpos arg2)); intros H
   | intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r')(Zpos arg2)); intros H
   | case arg2; lazy beta iota delta [div_bin]; intros].

Theorem div_bin_rem_lt :
 forall n m:positive, 0 <= snd (div_bin n m) < Zpos m.
Proof. intros n m; div_bin_tac n m; unfold snd; auto. lia. Qed.

Theorem div_bin_eq :
 forall n m:positive,
   Zpos n =  (fst (div_bin n m))*(Zpos m) + snd (div_bin n m).
Proof. intros n m; div_bin_tac n m; rewrite Zpos_xI || (try rewrite Zpos_xO); try rewrite Hrec; unfold fst; unfold snd; ring. Qed.

Inductive div_data (n m:positive) : Set :=
  div_data_def :
  forall q r:Z, Zpos n = q*(Zpos m)+r -> 0<= r < Zpos m -> div_data n m.

Close Scope Z_scope.

Section A_declared.

Variable A: Type.

Variable lt :  relation A.

Let le  x y := lt x y \/ x = y.

Context (lt_strict : StrictOrder lt).

Inductive CompSpec  (x y:A) : comparison -> Prop :=
 | CompEq : forall (H_eq: x = y), CompSpec  x y Eq
 | CompLt : forall (H_lt:lt x y), CompSpec  x y Lt
 | CompGt : forall (H_gt:lt y x), CompSpec  x y Gt.

Definition correct (cmp: A -> A -> comparison) :=
   forall x y:A, CompSpec x y (cmp x y).

Variable cmp : A -> A -> comparison.

Definition max  (x y:A)  : A :=
match cmp x y with Lt => y | _ => x end.

Definition min  (x y:A) : A :=
match cmp x y with Gt => y | _ => x end.

Section cmp_max_properties.

Hypothesis cmp_ok : correct cmp.

Lemma cmp_eq : forall x:A, cmp x x = Eq.
Proof. destruct lt_strict as [Hirr _]. intro x; destruct (cmp_ok x x). - reflexivity. - now destruct (Hirr x). - now destruct (Hirr x). Qed.

Lemma cmp_eq_iff : forall x y:A, cmp x y = Eq <-> x = y.
Proof. split. destruct lt_strict as [Hirr _]. destruct (cmp_ok x y); auto. - discriminate. - discriminate. - intro; subst y; now rewrite cmp_eq. Qed.

Lemma cmp_lt_iff : forall x y:A, cmp x y = Lt <-> lt x y.
Proof. destruct lt_strict as [ Hirr Htrans]; intros x y; destruct ( cmp_ok x y); custom_tac14 ; auto. custom_tac13 y; now destruct ( Hirr x); auto. intro; destruct ( Hirr x); eapply Htrans; eauto. Qed.

Lemma cmp_sym : forall x y , cmp x y = Gt <-> cmp y x = Lt.
Proof. destruct lt_strict as [Hirr Htrans]. intros x y; destruct (cmp_ok x y); destruct (cmp_ok y x); split; try discriminate; auto. intro. - subst y; now destruct (Hirr x). - destruct (Hirr x); transitivity y; auto. - subst y; now destruct (Hirr x). - destruct (Hirr x); transitivity y; auto. Qed.

Lemma max_eq : forall x y: A, let  m:= max  x y 
                              in m = x \/ m = y.
Proof. intros x y; unfold max; destruct (cmp_ok x y); cbn; auto. Qed.

Lemma le_max : forall x y:A, le x (max  x y).
Proof. intros x y; unfold le, max; destruct (cmp_ok x y); cbn; auto. Qed.

Lemma max_le : forall x y z:A, le x z -> le y z -> le (max x y) z.
Proof. intros x y z H H0; destruct (max_eq x y) as [e | e]; now rewrite e. Qed.

End cmp_max_properties.

End A_declared.

Arguments max {A} _ _ _.

Fixpoint cmp (n p :nat) : comparison :=
  match n, p with 0, 0 => Eq
                | 0, S _ => Lt
                | S _, 0 => Gt
                | S q, S r => cmp q r
  end.

Lemma cmp_correct : correct nat lt cmp.
Proof. red. induction x;destruct y;simpl;try constructor;auto with arith. destruct (IHx y). subst y;constructor;trivial. constructor;auto with arith. constructor;auto with arith. Qed.

Fixpoint rem2 (n:nat):nat:=
  match n with 0 => 0 | 1 => 1 | S (S p) => rem2 p end.

Theorem div2_ind :
  forall P: nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S (S n))) ->
    forall n, P n.
Proof. intros P H0 H1 Hstep n. assert (P n /\ P(S n)). elim n; intuition. intuition. Qed.

Fixpoint fib (n:nat) : nat :=
  match n with
    0 => 1
  | 1 => 1
  | S ((S p) as q) => fib p + fib q
  end.

Fixpoint fib2 (n:nat) : nat*nat :=
  match n with
    0 => (1, 1)
  | S p => 
    let (v1, v2) := fib2 p in (v2, v1 + v2)
  end.

Theorem fib_ind :
  forall P : nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n)))->
    forall n, P n.
Proof. intros P H0 H1 Hstep n. assert (P n /\ P(S n)). elim n; intuition. intuition. Qed.

Theorem div2_rem2_eq : forall n, 2 * div2 n + rem2 n = n.
Proof. intros n; elim n using div2_ind; try (simpl; auto with arith; fail). intros p IHp; pattern p at 3; rewrite <- IHp. simpl;ring. Qed.

Theorem fib_fib2_equiv : forall n, fib n = (fst (fib2 n)).
Proof. intros n; elim n using fib_ind; try(simpl;auto with arith;fail). intros p IHp IHSp. replace (fib (S (S p))) with (fib p + fib (S p)). rewrite IHp; rewrite IHSp. simpl. case (fib2 p); auto. auto. Qed.

Section div3.

Fixpoint div3 (n:nat): nat :=
  match n with
    | 0 | 1 | 2 => 0
    | S (S (S p)) => S (div3 p)
  end.

Lemma nat_ind3 (P : nat -> Prop) :
  P 0 -> P 1 -> P 2 ->
  (forall i:nat, P i -> P (3 + i)) ->
  forall n:nat, P n.
Proof. intros H0 H1 H2 HS n. assert (H: P n /\ P (S n) /\ P (S (S n))). induction n. split;auto. destruct IHn as [Hn [HSn HSSn]];repeat split;auto. - apply HS;auto. - tauto. Qed.

Lemma div3_le : forall n, div3 n <= n.
Proof. induction n using nat_ind3; auto. - simpl; apply Nat.le_trans with (S n); auto with arith. Qed.

End div3.

Section even_odd.

Require Import Arith Lia.

Definition Even (n:nat) : Prop :=
 exists p:nat, n = 2*p.

Definition Odd (n:nat) : Prop :=
 exists p:nat, n = S (2*p).

Lemma Even_not_Odd : forall n, Even n -> ~ Odd n.
Proof. intros n [p Hp] [q Hq]; rewrite Hp in Hq. lia. Qed.

Inductive even_spec (n:nat) : bool -> Prop :=
| even_true : forall (Heven : Even n), even_spec n true 
| even_false : forall (Hodd : Odd n), even_spec n false.

Definition even_test_ok (f : nat -> bool) :=
 forall n:nat, even_spec n (f n).

Fixpoint even_bool (n:nat) :=
 match n with
   | 0 => true
   | 1 => false
   | S (S p)=> even_bool p
end.

Lemma nat_double_rect : forall (P:nat->Type),
     P 0 -> P 1 -> (forall p, P p -> P (S (S p))) ->
    forall n:nat, P n.
Proof. intros P H0 H1 HS. assert (X : forall n, (P n * P (S n)%type)). - induction n as [| p IHp]. + auto. + destruct IHp; auto. - intro n; now destruct (X n). Qed.

Lemma even_spec_SS : forall n b, even_spec n b -> even_spec (S (S n)) b.
Proof. intros n p [[q Hq] | [q Hq]]; constructor;exists (S q);lia. Qed.

Lemma even_bool_correct : even_test_ok  even_bool.
Proof. intro n;induction n using nat_double_rect. constructor;exists 0;trivial. constructor;exists 0;trivial. cbn;apply even_spec_SS;assumption. Qed.

Lemma even_bool_false (f: nat->bool) (H: even_test_ok f):
 forall n,  Odd n <-> f n = false.
Proof. intros n ;destruct (H n). - split; try discriminate; intro;destruct (Even_not_Odd n); auto. - tauto. Qed.

End even_odd.

Definition eqdec (A:Type) := forall a b : A, {a = b}+{a <> b}.

Definition nat_eq_dec : eqdec nat.
Proof. red; simple induction a; simple destruct b. - now left. - right; red; discriminate 1. - right; red; discriminate 1. - intro n0; case (H n0); auto. Qed.

Section fib_ind.

Lemma fib_rect :
 forall P:nat -> Type,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof. intros P H0 H1 HSSn n. assert (X: P n * P (S n)). - induction n as [ | n IHn]. + split; auto. + destruct IHn; split; auto. - now destruct X. Qed.

Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof. intros. reflexivity. Qed.

Fixpoint fib_pair (n:nat) : nat * nat :=
  match n with
  | O => (1, 1)
  | S p => match fib_pair p with
           | (x, y) => (y, x + y)
           end
  end.

Definition linear_fib (n:nat) := fst (fib_pair n).

Lemma fib_pair_correct : forall n:nat, fib_pair n = (fib n, fib (S n)).
Proof. induction n as [| n IHn]; cbn. - reflexivity. - rewrite IHn; reflexivity. Qed.

Theorem linear_fib_correct : forall n:nat, linear_fib n = fib n.
Proof. unfold linear_fib; intro n; now rewrite fib_pair_correct. Qed.

End fib_ind.

Section fib_tail.

Fixpoint general_fib (a0 a1 n:nat) {struct n} : nat :=
  match n with
  | O => a0
  | S p => general_fib a1 (a0 + a1) p
  end.

Definition fib_tail (n:nat) := general_fib 1 1 n.

Lemma general_fib_1 : forall a b:nat, general_fib a b 1 = b.
Proof. intros. reflexivity. Qed.

Lemma general_fib_S :
 forall a b n:nat, general_fib a b (S n) = general_fib b (a + b) n.
Proof. intros. reflexivity. Qed.

Lemma general_fib_2 :
 forall a b n:nat,
   general_fib a b (S (S n)) = general_fib a b n + general_fib a b (S n).
Proof. intros a b n; generalize a b; induction n as [ | n IHn]. - reflexivity. - clear a b; intros a b. rewrite (general_fib_S _ _ (S (S n))), IHn. now rewrite (general_fib_S _ _ (S n)). Qed.

Lemma linear_fibo_equiv : forall n:nat, fib_tail n = fib n.
Proof. intro n; induction n as [| | n IHn IHSn] using fib_ind. - reflexivity. - reflexivity. - unfold fib_tail in *; rewrite general_fib_2. rewrite IHn. rewrite IHSn. reflexivity. Qed.

End fib_tail.

Section fib_positive.

Lemma le_add_sub_r (n m:nat) : n <= m -> n + (m - n) = m.
Proof. intro H; rewrite Nat.add_comm; rewrite Nat.sub_add; try assumption. reflexivity. Qed.

Lemma sub_add (n m : nat) : n + m - n = m.
Proof. intros. rewrite Nat.add_comm; rewrite Nat.add_sub. reflexivity. Qed.

End fib_positive.

Section perms.

Variable A : Type.

Inductive transpose : list A -> list A ->  Prop :=
  transpose_hd:
    forall (a b : A) (l : list A),  transpose (a :: (b :: l)) (b :: (a :: l))
 | transpose_tl:
     forall (a : A) (l l' : list A),
     transpose l l' ->  transpose (a :: l) (a :: l') .

Inductive perm (l : list A) : list A ->  Prop :=
  perm_id: perm l l
 | perm_tr:
     forall (l' l'' : list A), perm l l' -> transpose l' l'' ->  perm l l'' .

Variable A_eq_dec : forall a b:A, {a = b} + {a <> b}.

Fixpoint nb_occ (a : A) (l : list A)  : nat :=
 match l with
  | nil => 0
  | x :: l' =>
      match A_eq_dec  a x with
        | left _ => S (nb_occ a l')
        | right _ => nb_occ a l'
      end
 end.

Lemma transpose_nb_occ:
 forall (l l' : list A),
 transpose l l' -> forall (a : A),  nb_occ a l = nb_occ a l'.
Proof. intros l l' H; elim H; simpl. - intros a b l0 x; case (A_eq_dec x a); case (A_eq_dec x b); simpl; auto. - intros a l0 l'0 H0 H1 x; case (A_eq_dec x a); simpl; auto. Qed.

Lemma perm_nb_occ:
 forall (l l' : list A),
 perm l l' -> forall (a : A),  nb_occ a l = nb_occ a l'.
Proof. intros l l' H; elim H; auto. intros l'0; intros; transitivity (nb_occ a l'0);auto. apply transpose_nb_occ; auto. Qed.

Fixpoint check_all_occs (l1 l2 l3 : list A)  : bool :=
 match l3 with
   nil => true
  | a :: tl =>
      if Nat.eqb  (nb_occ a l1) (nb_occ a l2) then check_all_occs l1 l2 tl
        else false
 end.

Theorem eq_nat_bool_false:
 forall n1 n2, Nat.eqb n1 n2 = false ->   n1 <> n2.
Proof. induction n1; destruct n2; simpl; intros; try discriminate; auto. Qed.

Theorem check_all_occs_false:
 forall l1 l2 l3,
 check_all_occs l1 l2 l3 = false ->
  (exists a : A , nb_occ a l1 <> nb_occ a l2 ).
Proof. simple induction l3. - simpl; intros; discriminate. - intros n l IHl; simpl. generalize (@eq_nat_bool_false (nb_occ n l1) (nb_occ n l2)). case (Nat.eqb (nb_occ n l1) (nb_occ n l2)). + auto. + intros; exists n; auto. Qed.

Theorem check_all_occs_not_perm:
 forall l1 l2, check_all_occs l1 l2 l1 = false ->  ~ perm l1 l2.
Proof. intros l1 l2 Heq Hperm; elim (check_all_occs_false l1 l2 l1 Heq); intros n Hneq; elim Hneq; apply perm_nb_occ; assumption. Qed.

End perms.



