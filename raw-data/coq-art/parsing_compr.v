Require Export List.

Require Export Arith.

Inductive par : Set :=
  | open : par
  | close : par.

Inductive wp : list par -> Prop :=
  | wp_nil : wp nil
  | wp_concat : forall l1 l2:list par, wp l1 -> wp l2 -> wp (l1 ++ l2)
  | wp_encapsulate :
      forall l:list par, wp l -> wp (open :: l ++ close :: nil).

Ltac custom_tac24 H0 := case H0; simpl.

Ltac custom_tac7 H0 := apply H0; auto.

Ltac custom_tac6  := simpl; auto.

Ltac custom_tac1 H0 := apply H0; trivial.

Ltac custom_tac8 H0 := rewrite H0; auto.

Ltac custom_tac11 H0 H1 := intros H0 H1; elim H1.

Ltac custom_tac29 H0 H1 := apply H0 with ( 1 := H1); simpl; auto with arith.

Ltac custom_tac19 H0 H1 H2 := injection H0; intros H1 H2.

Ltac custom_tac18 H0 H1 H2 := auto; intros H0 H1 H2.

Theorem wp_oc : wp (open :: close :: nil).
Proof. change (wp (open :: nil ++ close :: nil)) in |- *. apply wp_encapsulate. apply wp_nil. Qed.

Theorem wp_o_head_c :
 forall l1 l2:list par, wp l1 -> wp l2 -> wp (open :: l1 ++ close :: l2).
Proof. intros l1 l2 H1 H2. replace (open :: l1 ++ close :: l2) with ((open :: l1 ++ close :: nil) ++ l2). - apply wp_concat. apply wp_encapsulate; trivial. trivial. - repeat (simpl in |- *; rewrite <- app_assoc); simpl in |- *. trivial. Qed.

Theorem wp_o_tail_c :
 forall l1 l2:list par,
   wp l1 -> wp l2 -> wp (l1 ++ open :: l2 ++ close :: nil).
Proof. intros l1 l2 H1 H2; apply wp_concat. - trivial. - now apply wp_encapsulate. Qed.

Inductive bin : Set :=
  | L : bin
  | N : bin -> bin -> bin.

Fixpoint bin_to_string (t:bin) : list par :=
  match t with
  | L => nil (A:=par)
  | N u v => open :: bin_to_string u ++ close :: bin_to_string v
  end.

Theorem bin_to_string_wp : forall t:bin, wp (bin_to_string t).
Proof. simple induction t. - simpl; apply wp_nil. - simpl; intros t1 H1 t2 H2; apply wp_o_head_c; trivial. Qed.

Hint Resolve wp_nil wp_concat wp_encapsulate wp_o_head_c wp_o_tail_c wp_oc : core.

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

Hint Resolve wp'_nil wp'_cons wp'_concat : core.

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

Hint Resolve wp''_nil wp''_cons : core.

Lemma wp''_concat :
 forall l1 l2:list par, wp'' l1 -> wp'' l2 -> wp'' (l1 ++ l2).
Proof. intros l1 l2 H1 H2; generalize l1 H1; clear H1 l1; elim H2. - intros; rewrite app_nil_r; trivial. - intros; rewrite app_assoc; auto. Qed.

Theorem wp''_encapsulate :
 forall l:list par, wp'' l -> wp'' (open :: l ++ close :: nil).
Proof. intros l H; change (wp'' (nil ++ open :: l ++ close :: nil)); auto. Qed.

Hint Resolve wp''_concat wp''_encapsulate : core.

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
Proof. intros A l a. rewrite <- (rev_involutive (a :: l)). assert (H : 0 < length (rev (a :: l))) by (rewrite <- length_rev; simpl ; auto with arith). destruct (rev (a :: l)) as [ | a0 l0]. - simpl ; elim (Nat.nlt_0_r 0); auto. - exists a0, (rev l0); simpl; auto. Qed.

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
   recognize n l = true -> wp (make_list _ open n ++ l). Proof. simple induction l; simpl. - intros n; case n. simpl ; intros; apply wp_nil. intros n' H; discriminate H. - intros a; case a; simpl ; clear a. + intros l' H n H0. rewrite <- make_list_end; auto. + intros l' H n; case n; clear n. intros H'; discriminate H'. intros n H0; rewrite make_list_end; apply wp_remove_oc;auto. Qed.

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



