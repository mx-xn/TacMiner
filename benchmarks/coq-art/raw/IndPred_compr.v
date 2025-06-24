Require Export ZArith.

Require Export List.

Require Export Arith.

Require Export Lia.

Require Export Zwf.

Section chap8.

Inductive plane : Set :=
    point : Z->Z->plane.

Inductive htree (A:Type) : nat->Type :=
  | hleaf : A -> htree A 0%nat
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Inductive south_west : plane->plane->Prop :=
  south_west_def :
  forall a1 a2 b1 b2:Z, (a1 <= b1)%Z -> (a2 <= b2)%Z ->
        south_west (point a1 a2)(point b1 b2).

Inductive even : nat->Prop :=
  | O_even : even 0
  | plus_2_even : forall n:nat, even n -> even (S (S n)).

Inductive sorted {A:Type}(R:A->A->Prop) : list A -> Prop :=
  | sorted0 : sorted  R nil
  | sorted1 : forall x:A, sorted  R (x :: nil)
  | sorted2 :
      forall (x y:A)(l:list A),
        R x y ->
        sorted  R (y :: l)-> sorted  R (x  ::  y :: l).

Hint Constructors sorted :  sorted_base.

Require Export Relations.

Inductive clos_trans {A:Type}(R:relation A) : A->A->Prop :=
  | t_step : forall x y:A, R x y -> clos_trans  R x y
  | t_trans :
    forall x y z:A, clos_trans  R x y -> clos_trans  R y z ->
        clos_trans  R x z.

Theorem zero_cons_ord :
 forall l:list nat, sorted le l -> sorted le (cons 0 l).
Proof. induction 1; auto with sorted_base arith. Qed.

Theorem sorted1_inv {A:Type}{le : relation A} { x l} (H: sorted le (x::l))  :
  sorted le l.
Proof. inversion H; auto with sorted_base. Qed.

Theorem sorted2_inv {A:Type}{le : relation A} {x y  l}
        (H: sorted le (x::y::l)): le x y.
Proof. inversion H; auto with sorted_base. Qed.

Theorem not_sorted_132 :  ~ sorted le (1::3::2::nil).
Proof. intros H; generalize (sorted1_inv H); intro H0. generalize (sorted2_inv H0). lia. Qed.

Require Import JMeq.

Inductive ahtree(A:Type) : Type :=
  any_height : forall n:nat, htree A n -> ahtree A.

Arguments any_height {A} n _.

Theorem any_height_inj2 {A:Type} :
 forall (n1 n2:nat)(t1:htree A n1)(t2:htree A n2),
   any_height n1 t1 = any_height n2 t2 -> JMeq t1 t2.
Proof. intros n1 n2 t1 t2 H. injection H; intros H1 H2. dependent rewrite <- H1. trivial. Qed.

Theorem any_height_inj2' {A:Type} :
 forall (n1 n2:nat)(t1:htree A n1)(t2:htree A n2),
   any_height n1 t1 = any_height   n2 t2 -> JMeq t1 t2.
Proof. intros n1 n2 t1 t2 H. change (match any_height n2 t2 with | any_height n t => JMeq t1 t end); now rewrite <- H. Qed.

Require Import List  Vector.

Section vectors_and_lists.

Variable A : Type.

Fixpoint vector_to_list (n:nat)(v:t A n){struct v}
  : list A :=
  match v with
  | nil _ => List.nil
  | cons _ a p tl => List.cons a (vector_to_list p tl)
  end.

Fixpoint list_to_vector (l:list A) : t A (length l) :=
   match l as x return t A (length x) with
   | List.nil => nil A
   | List.cons a tl => cons A a (length tl)(list_to_vector tl)
   end.

Theorem keep_length :
  forall (n:nat)(v:t A n), length (vector_to_list n v) = n.
Proof. intros n v; induction v; simpl; auto. Qed.

Lemma Vconseq :
  forall (a:A)(n m:nat),
   n = m ->
   forall (v:t A n)(w:t A m),
     JMeq v w -> JMeq (cons A a n v)(cons A a m w).
Proof. intros a n m Heq; rewrite Heq. intros v w HJeq. rewrite HJeq; reflexivity. Qed.

Theorem vect_to_list_and_back :
  forall n (v:t A n),
    JMeq v (list_to_vector (vector_to_list n v)).
Proof. intros n v; induction v as [ | h n v IHv]. - reflexivity. - simpl; apply Vconseq. + now rewrite keep_length. + assumption. Qed.

End vectors_and_lists.

Theorem structured_intro_example1 : forall A B C:Prop, A/\B/\C->A.
Proof. intros A B C [Ha [Hb Hc]]; assumption. Qed.

Theorem structured_intro_example2 : forall A B:Prop, A \/ B/\(B->A)->A.
Proof. intros A B [Ha | [Hb Hi]]. - assumption. - now apply Hi. Qed.

Theorem sum_even : forall n p:nat, even n -> even p -> even (n+p).
Proof. (** False start intros n; elim n. auto. intros n' Hrec p Heven_Sn' Heven_p. Restart. *) intros n p Heven_n; induction Heven_n. - trivial. - intro H0; simpl; constructor; auto. Qed.

Theorem lt_le : forall n p:nat, n < p -> n <= p.
Proof. intros n p H; induction H; repeat constructor; assumption. Qed.

Open Scope Z_scope.

Inductive Pfact : Z->Z->Prop :=
  Pfact0 : Pfact 0 1
| Pfact1 : forall n v:Z, n <> 0 -> Pfact (n-1) v -> Pfact n (n*v).

Theorem pfact3 : Pfact 3 6.
Proof. apply Pfact1 with (n := 3)(v := 2). discriminate. apply (Pfact1 2 1). discriminate. apply (Pfact1 1 1). discriminate. apply Pfact0. Qed.

Theorem fact_def_pos : forall x y:Z, Pfact x y ->  0 <= x.
Proof. intros x y H; induction H. - auto with zarith. - lia. Qed.

Theorem Zle_Pfact : forall x:Z, 0 <= x -> exists y:Z, Pfact x y.
Proof. intros x; induction x using (well_founded_ind (Zwf_well_founded 0)). intros Hle; destruct (Zle_lt_or_eq _ _ Hle). - destruct (H (x-1)). + unfold Zwf; lia. + lia. + exists (x*x0); apply Pfact1; auto with zarith. - subst x; exists 1; constructor. Qed.

Section little_semantics.

Variables Var aExp bExp : Set.

Inductive inst : Set :=
 | Skip : inst
 | Assign : Var->aExp->inst
 | Sequence : inst->inst->inst
 | WhileDo : bExp->inst->inst.

Variables
  (state : Set)
  (update : state->Var->Z -> option state)
  (evalA : state->aExp -> option Z)
  (evalB : state->bExp -> option bool).

Inductive exec : state->inst->state->Prop :=
 | execSkip : forall s:state, exec s Skip s
 | execAssign :
    forall (s s1:state)(v:Var)(n:Z)(a:aExp),
     evalA s a = Some n -> update s v n = Some s1 ->
     exec s (Assign v a) s1
 | execSequence :
    forall (s s1 s2:state)(i1 i2:inst),
     exec s i1 s1 -> exec s1 i2 s2 ->
     exec s (Sequence i1 i2) s2
 | execWhileFalse :
    forall (s:state)(i:inst)(e:bExp),
     evalB s e = Some false -> exec s (WhileDo e i) s
 | execWhileTrue :
    forall (s s1 s2:state)(i:inst)(e:bExp),
     evalB s e = Some true ->
     exec s i s1 ->
     exec s1 (WhileDo e i) s2 ->
     exec s (WhileDo e i) s2.

Theorem HoareWhileRule :
  forall (P:state->Prop)(b:bExp)(i:inst)(s s':state),
    (forall s1 s2:state,
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2)->
    P s -> exec s (WhileDo b i) s' ->
    P s' /\ evalB s' b = Some false.
Proof. intros P b i s s' H. cut (forall i':inst, exec s i' s' -> i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false); eauto. intros i' Hexec; elim Hexec; try (intros; discriminate). intros s0 i0 e Heval Heq; injection Heq; intros H1 H2. rewrite <- H2; auto. intros. injection H5. intros H' H''. subst i0 b; eauto. Qed.

End little_semantics.

Open Scope nat_scope.

Inductive is_0_1 : nat->Prop :=
  is_0 : is_0_1 0 | is_1 : is_0_1 1.

Hint Resolve is_0 is_1 : core.

Lemma sqr_01 : forall x:nat, is_0_1 x -> is_0_1 (x * x).
Proof. induction 1; simpl; auto. Qed.

Theorem elim_example : forall n:nat, n <= 1 -> n*n <= 1.
Proof. intros n H. destruct (sqr_01 n); auto. inversion_clear H; auto. inversion_clear H0; auto. Qed.

Theorem not_even_1 : ~even 1.
Proof. unfold not; intros H. inversion H. Qed.

Theorem plus_2_even_inv : forall n:nat, even (S (S n))-> even n.
Proof. intros n H; inversion H; assumption. Qed.

Theorem not_even_1' : ~even 1.
Proof. intro H. generalize (refl_equal 1). pattern 1 at -2. induction H. - discriminate. - discriminate. Qed.

Theorem plus_2_even_inv' : forall n:nat, even (S (S n))-> even n.
Proof. intros n H. generalize (refl_equal (S (S n))). pattern (S (S n)) at -2. induction H. - discriminate. - intros H0; injection H0; intro; now subst n0. Qed.

Close Scope nat_scope.

End chap8.

Require Export List Relations.

Section impredicative.

Section R_declared.

Variables (A: Type)
            (R: relation A).

Inductive sorted_im : list A -> Prop :=
    sorted0_im : sorted_im nil
  | sorted1_im : forall x:A, sorted_im (x::nil)
  | sorted2_im : forall (x1 x2:A)(l':list A),
      R x1 x2 -> sorted_im (x2::l') -> sorted_im (x1::x2::l').

#[local] Hint Constructors sorted_im : core.

Definition impredicative_sorted (l:list A) : Prop :=
    forall P :  list A -> Prop,
      P nil ->
      (forall x:A, P (x::nil))->
      (forall (x1 x2:A)(l':list A),
          R x1 x2 -> P (x2::l') -> P (x1::x2::l'))->
      P l.

Theorem isorted0 :  impredicative_sorted nil.
Proof. red; intros; assumption. Qed.

Theorem isorted1 :  forall  x: A , impredicative_sorted (x::nil).
Proof. unfold impredicative_sorted; auto. Qed.

Theorem isorted2  :
    forall (x1 x2:A)(l':list A),
      R x1 x2 ->
      impredicative_sorted  (x2::l') ->
      impredicative_sorted  (x1::x2::l').
Proof. intros x1 x2 l' Hr Hs P Hsn Hs1 Hs2. apply Hs2; auto. apply Hs; auto. Qed.

#[local] Hint Resolve isorted0 isorted1 isorted2 : core.

Theorem sorted_to_impredicative_sorted :
    forall l, sorted_im l -> impredicative_sorted l.
Proof. induction 1; auto. Qed.

Theorem impredicative_sorted_to_sorted :
    forall l, impredicative_sorted l -> sorted_im l.
Proof. intros l H; apply H; auto. Qed.

End R_declared.

End impredicative.

Inductive par : Set :=
  | open : par
  | close : par.

Inductive wp : list par -> Prop :=
  | wp_nil : wp nil
  | wp_concat : forall l1 l2:list par, wp l1 -> wp l2 -> wp (l1 ++ l2)
  | wp_encapsulate :
      forall l:list par, wp l -> wp (open :: l ++ close :: nil).

Theorem wp_oc : wp (open :: close :: nil).
Proof. change (wp (open :: nil ++ close :: nil)) in |- *. apply wp_encapsulate. apply wp_nil. Qed.

Theorem wp_o_head_c :
 forall l1 l2:list par, wp l1 -> wp l2 -> wp (open :: l1 ++ close :: l2).
Proof. intros l1 l2 H1 H2. replace (open :: l1 ++ close :: l2) with ((open :: l1 ++ close :: nil) ++ l2). - apply wp_concat. apply wp_encapsulate; trivial. trivial. - repeat (simpl in |- *; rewrite <- app_assoc); simpl in |- *. trivial. Qed.

Ltac custom_tac6 H0 := apply H0; trivial.

Theorem wp_o_tail_c :
 forall l1 l2:list par,
   wp l1 -> wp l2 -> wp (l1 ++ open :: l2 ++ close :: nil).
Proof. intros l1 l2 H1 H2; custom_tac6 wp_concat. - now apply wp_encapsulate. Qed.

Inductive bin : Set :=
  | L : bin
  | N : bin -> bin -> bin.

Fixpoint bin_to_string (t:bin) : list par :=
  match t with
  | L => nil (A:=par)
  | N u v => open :: bin_to_string u ++ close :: bin_to_string v
  end.

Theorem bin_to_string_wp : forall t:bin, wp (bin_to_string t).
Proof. simple induction t. - simpl ; apply wp_nil. - simpl ; intros t1 H1 t2 H2; apply wp_o_head_c; trivial. Qed.

#[export] Hint Resolve wp_nil wp_concat wp_encapsulate wp_o_head_c wp_o_tail_c wp_oc : core.

Fixpoint bin_to_string' (t:bin) : list par :=
  match t with
  | L => nil (A:=par)
  | N u v =>
      bin_to_string' u ++ open :: bin_to_string' v ++ close :: nil
  end.

Theorem bin_to_string'_wp : forall t:bin, wp (bin_to_string' t).
Proof. simple induction t; simpl ; auto. Qed.

Inductive parse_rel : list par -> list par -> bin -> Prop :=
  | parse_node :
      forall (l1 l2 l3:list par) (t1 t2:bin),
        parse_rel l1 (close :: l2) t1 ->
        parse_rel l2 l3 t2 -> parse_rel (open :: l1) l3 (N t1 t2)
  | parse_leaf_nil : parse_rel nil nil L
  | parse_leaf_close :
      forall l:list par, parse_rel (close :: l) (close :: l) L.

Theorem parse_rel_sound_aux :
 forall (l1 l2:list par) (t:bin),
   parse_rel l1 l2 t -> l1 = bin_to_string t ++ l2.
Proof. intros l1 l2 t H; elim H; clear H l1 l2 t. - intros l1 l2 l3 t1 t2 Hp Hr1 Hp2 Hr2; simpl. rewrite <- app_assoc, Hr1; simpl. now rewrite Hr2. - reflexivity. - reflexivity. Qed.

Theorem parse_rel_sound :
 forall l:list par, (exists t : bin, parse_rel l nil t) -> wp l.
Proof. intros l [t H]; replace l with (bin_to_string t). - apply bin_to_string_wp. - symmetry; replace (bin_to_string t) with (bin_to_string t ++ nil). + apply parse_rel_sound_aux; auto. + rewrite app_nil_r; auto. Qed.

Inductive wp' : list par -> Prop :=
  | wp'_nil : wp' nil
  | wp'_cons :
      forall l1 l2:list par,
        wp' l1 -> wp' l2 -> wp' (open :: l1 ++ close :: l2).

Theorem wp'_concat :
 forall l1 l2:list par, wp' l1 -> wp' l2 -> wp' (l1 ++ l2).
Proof. intros l1 l2 H; generalize l2; clear l2. elim H. - simpl; auto. - intros l1' l2' Hb1' Hr1 Hb2' Hr2 l2 Hb2; simpl; rewrite <- app_assoc. simpl; apply wp'_cons; auto. Qed.

#[export] Hint Resolve wp'_nil wp'_cons wp'_concat : core.

Theorem wp'_encapsulate :
 forall l:list par, wp' l -> wp' (open :: l ++ close :: nil).
Proof. intros l H; elim H; auto. Qed.

Theorem wp_imp_wp' : forall l:list par, wp l -> wp' l.
Proof. intros l H; elim H. - apply wp'_nil. - intros; apply wp'_concat; trivial. - intros; apply wp'_encapsulate; trivial. Qed.

Theorem wp'_imp_wp : forall l:list par, wp' l -> wp l.
Proof. intros l H; elim H; auto. Qed.

Inductive wp'' : list par -> Prop :=
  | wp''_nil : wp'' nil
  | wp''_cons :
      forall l1 l2:list par,
        wp'' l1 -> wp'' l2 -> wp'' (l1 ++ open :: l2 ++ close :: nil).

#[export] Hint Resolve wp''_nil wp''_cons : core.

Lemma wp''_concat :
 forall l1 l2:list par, wp'' l1 -> wp'' l2 -> wp'' (l1 ++ l2).
Proof. intros l1 l2 H1 H2; generalize l1 H1; clear H1 l1; elim H2. - intros; rewrite app_nil_r; trivial. - intros; rewrite app_assoc; auto. Qed.

Theorem wp''_encapsulate :
 forall l:list par, wp'' l -> wp'' (open :: l ++ close :: nil).
Proof. intros l H; change (wp'' (nil ++ open :: l ++ close :: nil)); auto. Qed.

#[export] Hint Resolve wp''_concat wp''_encapsulate : core.

Theorem wp_imp_wp'' : forall l:list par, wp l -> wp'' l.
Proof. simple induction 1; auto. Qed.

Theorem wp''_imp_wp : forall l:list par, wp'' l -> wp l.
Proof. simple induction 1; auto. Qed.

Fixpoint recognize (n:nat) (l:list par) {struct l} : bool :=
  match l with
  | nil => match n with
           | O => true
           | _ => false
           end
  | open :: l' => recognize (S n) l'
  | close :: l' => match n with
                   | O => false
                   | S n' => recognize n' l'
                   end
  end.

Theorem recognize_complete_aux :
 forall l:list par,
   wp l ->
   forall (n:nat) (l':list par), recognize n (l ++ l') = recognize n l'.
Proof. intros l H; elim H. - simpl; auto. - intros l1 l2 H1 Hrec1 H2 Hrec2 n l'. rewrite <- app_assoc; transitivity (recognize n (l2 ++ l')); auto. - intros l1 H1 Hrec n l'; simpl ; rewrite <- app_assoc; rewrite Hrec; simpl ; auto. Qed.

Theorem recognize_complete : forall l:list par, wp l -> recognize 0 l = true.
Proof. intros l H; rewrite <- (app_nil_r l), recognize_complete_aux; auto. Qed.

Theorem app_decompose :
 forall (A:Type) (l1 l2 l3 l4:list A),
   l1 ++ l2 = l3 ++ l4 ->
   (exists l1' : list A, l1 = l3 ++ l1' /\ l4 = l1' ++ l2) \/
   (exists a : A,
      exists l2' : list A, l3 = l1 ++ a :: l2' /\ l2 = (a :: l2') ++ l4).
Proof. simple induction l1. - intros l2 l3; case l3. + intros l4 H; left; exists (nil (A:=A)); auto. + intros a l3' Heq; right; exists a; exists l3'; auto. - clear l1; intros a l1 Hrec l2 l3; case l3. + intros l4 H; left; exists (a :: l1); auto. + simpl ; intros a' l3' l4 Heq; injection Heq; intros Heq' Heq''. elim Hrec with (1 := Heq'). intros [l1' [Heq3 Heq4]]; left; exists l1'; split; auto. rewrite Heq''; rewrite Heq3; auto. intros [a'' [l2' [Heq3 Heq4]]]; right; exists a'', l2'; split; auto. rewrite Heq''; rewrite Heq3; auto. Qed.

Theorem length_app :
 forall {A:Type} (l1 l2:list A), length (l1 ++ l2) = length l1 + length l2.
Proof. simple induction l1; simpl in |- *; auto. Qed.

Theorem length_rev : forall {A:Type} (l:list A), length l = length (rev l).
Proof. simple induction l; auto. - intros a l' H; simpl in |- *. rewrite length_app. simpl in |- *; rewrite <- plus_n_Sm; rewrite H; auto with arith. Qed.

Theorem cons_to_app_end :
 forall {A:Type} (l:list A) (a:A),
    exists b : A, exists l' : list A, a :: l = l' ++ b :: nil.
Proof. intros A l a. rewrite <- (rev_involutive (a :: l)). assert (H : 0 < length (rev (a :: l))) by (rewrite <- length_rev; simpl; auto with arith). destruct (rev (a :: l)) as [ | a0 l0]. - simpl ; elim (Nat.nlt_0_r 0); auto. - exists a0, (rev l0); simpl ; auto. Qed.

Theorem last_same :
 forall {A:Type} (a b:A) (l1 l2:list A),
   l1 ++ a :: nil = l2 ++ b :: nil -> l1 = l2 /\ a = b.
Proof. intros A a b l1 l2 H. assert (e: a :: rev l1 = b :: rev l2). - repeat rewrite <- rev_unit; now rewrite H. - injection e; intros H1 H2; split; auto. rewrite <- (rev_involutive l1), H1; apply rev_involutive. Qed.

Theorem wp_remove_oc_aux :
 forall l:list par,
   wp l ->
   forall l1 l2:list par, l1 ++ l2 = l -> wp (l1 ++ open :: close :: l2).
Proof. intros l H; elim H. - intros l1 l2 H1; elim (app_eq_nil _ _ H1); auto. simpl in |- *; intros Heq1 Heq2; rewrite Heq1; rewrite Heq2; apply wp_oc. - intros l1 l2 Hp1 Hr1 Hp2 Hr2 l3 l4 Heq. elim app_decompose with (1 := Heq). intros [l1' [Heq1 Heq2]]; rewrite Heq1, <- app_assoc; apply wp_concat; auto. intros [a' [l2' [Heq1 Heq2]]]. rewrite Heq2. repeat rewrite app_comm_cons. rewrite app_assoc. apply wp_concat; auto. - idtac. intros l' Hp'' Hrec l1; case l1. simpl ; intros l2 Heq; rewrite Heq. change (wp (open :: nil ++ close :: open :: l' ++ close :: nil)); auto. simpl; intros c l1' l2; case l2. + intros Heq; injection Heq; intros Heq1 Heq2. rewrite app_nil_r in Heq1; rewrite Heq1; rewrite Heq2. rewrite app_comm_cons. apply wp_concat; auto. + intros c' l2'; elim (cons_to_app_end l2' c'). intros c'' [l2'' Heq]; rewrite Heq. rewrite app_assoc; intros Heq1. injection Heq1; intros Heq2 Heq3; elim last_same with (1 := Heq2). intros Heq4 Heq5; rewrite Heq5; rewrite Heq3. change (wp (open :: l1' ++ (open :: close :: l2'') ++ close :: nil)) . rewrite app_assoc; auto. Qed.

Theorem wp_remove_oc :
 forall l1 l2:list par, wp (l1 ++ l2) -> wp (l1 ++ open :: close :: l2).
Proof. intros; apply wp_remove_oc_aux with (l := l1 ++ l2); auto. Qed.

Fixpoint make_list (A:Type) (a:A) (n:nat) {struct n} : 
 list A := match n with
           | O => nil (A:=A)
           | S n' => a :: make_list A a n'
           end.

Theorem make_list_end :
 forall (A:Type) (a:A) (n:nat) (l:list A),
   make_list A a (S n) ++ l = make_list A a n ++ a :: l.
Proof. simple induction n; simpl. - trivial. - intros n' H l; rewrite H; trivial. Qed.

Theorem recognize_sound_aux :
 forall (l:list par) (n:nat),
   recognize n l = true -> wp (make_list _ open n ++ l).
Proof. simple induction l; simpl. - intros n; case n. simpl ; intros; apply wp_nil. intros n' H; discriminate H. - intros a; case a; simpl ; clear a. + intros l' H n H0. rewrite <- make_list_end; auto. + intros l' H n; case n; clear n. intros H'; discriminate H'. intros n H0; rewrite make_list_end; apply wp_remove_oc;auto. Qed.

Theorem recognize_sound : forall l:list par, recognize 0 l = true -> wp l.
Proof. intros l H; generalize (recognize_sound_aux _ _ H); simpl; auto. Qed.

Fixpoint parse (s:list bin) (t:bin) (l:list par) {struct l} : 
 option bin :=
  match l with
  | nil => match s with
           | nil => Some t
           | _ => None (A:=bin)
           end
  | open :: l' => parse (t :: s) L l'
  | close :: l' =>
      match s with
      | t' :: s' => parse s' (N t' t) l'
      | _ => None (A:=bin)
      end
  end.

Theorem parse_reject_indep_t :
 forall (l:list par) (s:list bin) (t:bin),
   parse s t l = None ->
   forall (s':list bin) (t':bin),
     length s' = length s -> parse s' t' l = None.
Proof. simple induction l. - intros s; case s. + simpl; intros t H; discriminate H. + intros t0 s0 t H s'; case s'. * simpl; intros t' Hle; discriminate Hle. * simpl; auto. - intros a; case a; simpl; clear a; intros l' Hrec s. + intros t H s' t' Hle. apply Hrec with (1 := H). simpl; auto with arith. + case s. * intros t H s'; case s'; simpl; auto. intros t0 s0 t' Hle; discriminate Hle. * intros t0 s0 t H s'; case s'; simpl. intros t' H0; discriminate H0. intros t'0 s'0 t' Hle; apply Hrec with (1 := H). simpl in Hle; auto with arith. Qed.

Theorem parse_complete_aux :
 forall l:list par,
   wp' l ->
   forall (s:list bin) (t:bin) (l':list par),
     parse s t (l ++ l') = None ->
     forall (s':list bin) (t':bin),
       length s' = length s -> parse s' t' l' = None.
Proof. simple induction 1. - simpl; intros; eapply parse_reject_indep_t; eauto. - intros l1 l2 Hp1 Hr1 Hp2 Hr2 s t l' Hrej s' t' Hle. apply Hr2 with (s := s') (t := N t L). change (parse (t :: s') L (close :: l2 ++ l') = None) in |- *. simpl in Hrej. rewrite <- app_assoc in Hrej. apply Hr1 with (1 := Hrej). simpl; auto with arith. auto. Qed.

Theorem parse_complete : forall l:list par, wp l -> parse nil L l <> None.
Proof. intros l H; replace l with (l ++ nil). red in |- *; intros H'. assert (e : parse nil L nil = None). - apply parse_complete_aux with (2 := H'); auto. apply wp_imp_wp'; auto. - discriminate. - rewrite <- app_nil_r; auto. Qed.

Fixpoint unparse_stack (s:list bin) : list par :=
  match s with
  | nil => nil (A:=par)
  | t :: s' => unparse_stack s' ++ bin_to_string' t ++ open :: nil
  end.

Theorem parse_invert_aux :
 forall (l:list par) (s:list bin) (t t':bin),
   parse s t l = Some t' ->
   bin_to_string' t' = unparse_stack s ++ bin_to_string' t ++ l.
Proof. simple induction l. - intros s; case s. + simpl. intros t t' H; injection H; intros Heq. rewrite Heq. now rewrite app_nil_r. + simpl ; intros t0 s0 t t' H; discriminate H. - intros a; case a; simpl; clear a; intros l' Hrec s. + intros t t' H; rewrite Hrec with (1 := H). simpl; repeat (rewrite <- app_assoc; simpl); auto. + case s. * intros t t' H; discriminate H. * intros t0 s0 t t' Hp; rewrite Hrec with (1 := Hp); simpl; repeat (rewrite <- app_assoc; simpl); auto. Qed.

Theorem parse_invert :
 forall (l:list par) (t:bin), parse nil L l = Some t -> bin_to_string' t = l.
Proof. intros; replace l with (unparse_stack nil ++ bin_to_string' L ++ l); auto. apply parse_invert_aux; auto. Qed.

Theorem parse_sound :
 forall (l:list par) (t:bin), parse nil L l = Some t -> wp l.
Proof. intros l t H; rewrite <- parse_invert with (1 := H). apply bin_to_string'_wp. Qed.



