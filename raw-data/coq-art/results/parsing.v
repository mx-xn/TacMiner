Theorem wp_oc : wp ( open :: close :: nil ) .
Proof.
   change ( wp ( open :: nil ++ close :: nil ) ) in | - *. apply wp_encapsulate. apply wp_nil.
Qed.
Theorem wp_o_head_c : forall l1 l2 : list par, wp l1 -> wp l2 -> wp ( open :: l1 ++ close :: l2 ) .
Proof.
   intros l1 l2 H1 H2. replace ( open :: l1 ++ close :: l2 ) with ( ( open :: l1 ++ close :: nil ) ++ l2 ).
    - apply wp_concat.
      -- custom7 wp_encapsulate.
      -- trivial.
    - repeat ( simpl in | - * ; rewrite <- app_assoc ).
      -- simpl in.
      -- - *. trivial.
Qed.
Theorem wp_o_tail_c : forall l1 l2 : list par, wp l1 -> wp l2 -> wp ( l1 ++ open :: l2 ++ close :: nil ) .
Proof.
   intros l1 l2 H1 H2. custom7 wp_concat. now apply wp_encapsulate.
Qed.
Theorem bin_to_string_wp : forall t : bin, wp ( bin_to_string t ) .
Proof.
   simple induction t.
    - simpl. apply wp_nil.
    - custom13 t1 H1 t2 H2. custom23.
Qed.
Theorem bin_to_string'_wp : forall t : bin, wp ( bin_to_string' t ) .
Proof.
   simple induction t.
    - custom1.
    - custom1.
Qed.
Theorem parse_rel_sound_aux : forall ( l1 l2 : list par ) ( t : bin ), parse_rel l1 l2 t -> l1 = bin_to_string t ++ l2 .
Proof.
   intros l1 l2 t H. elim H.
    - intros l1 l2 l3 t1 t2 Hp Hr1 Hp2 Hr2. simpl. rewrite <- app_assoc, Hr1. simpl. now rewrite Hr2.
    - reflexivity.
    - reflexivity.
Qed.
Theorem parse_rel_sound : forall l : list par, ( exists t : bin, parse_rel l nil t ) -> wp l .
Proof.
   intros l [ t H ]. replace l with ( bin_to_string t ).
    - apply bin_to_string_wp.
    - symmetry. replace ( bin_to_string t ) with ( bin_to_string t ++ nil ).
      -- custom3 parse_rel_sound_aux.
      -- custom16 app_nil_r.
Qed.
Theorem wp'_concat : forall l1 l2 : list par, wp' l1 -> wp' l2 -> wp' ( l1 ++ l2 ) .
Proof.
   intros l1 l2 H. generalize l2. custom26. simpl. rewrite <- app_assoc. simpl. custom10.
Qed.
Theorem wp'_encapsulate : forall l : list par, wp' l -> wp' ( open :: l ++ close :: nil ) .
Proof.
   custom6 l H.
Qed.
Theorem wp_imp_wp' : forall l : list par, wp l -> wp' l .
Proof.
   custom28 l H.
    - apply wp'_nil.
    - intros l1 l2 H0 H1 H2 H3. custom23.
    - intros l0 H0 H1. custom7 wp'_encapsulate.
Qed.
Theorem wp'_imp_wp : forall l : list par, wp' l -> wp l .
Proof.
   custom6 l H.
Qed.
Lemma wp''_concat : forall l1 l2 : list par, wp'' l1 -> wp'' l2 -> wp'' ( l1 ++ l2 ) .
Proof.
   intros l1 l2 H1 H2. generalize l1 H1. custom17 H2 l1 l0 H H0 H1 H3 l3 H4.
    - custom8 l1 H1 app_nil_r. trivial.
    - custom16 app_assoc.
Qed.
Theorem wp''_encapsulate : forall l : list par, wp'' l -> wp'' ( open :: l ++ close :: nil ) .
Proof.
   intros l H. change ( wp'' ( nil ++ open :: l ++ close :: nil ) ). auto.
Qed.
Theorem wp_imp_wp'' : forall l : list par, wp l -> wp'' l .
Proof.
   custom15. auto.
Qed.
Theorem wp''_imp_wp : forall l : list par, wp'' l -> wp l .
Proof.
   custom15.
Qed.
Theorem recognize_complete_aux : forall l : list par, wp l -> forall ( n : nat ) ( l' : list par ), recognize n ( l ++ l' ) = recognize n l' .
Proof.
   intros l H. custom26.
    - intros l1 H1 Hrec n l'. simpl. rewrite <- app_assoc. rewrite Hrec. custom1.
    - rewrite <- app_assoc. transitivity ( recognize n ( l2 ++ l' ) ).
      -- auto.
      -- auto.
Qed.
Theorem recognize_complete : forall l : list par, wp l -> recognize 0 l = true .
Proof.
   intros l H. rewrite <- ( app_nil_r l ), recognize_complete_aux.
    - auto.
    - auto.
Qed.
Theorem app_decompose : forall ( A : Type ) ( l1 l2 l3 l4 : list A ), l1 ++ l2 = l3 ++ l4 -> ( exists l1' : list A, l1 = l3 ++ l1' /\ l4 = l1' ++ l2 ) \/ ( exists a : A, exists l2' : list A, l3 = l1 ++ a :: l2' /\ l2 = ( a :: l2' ) ++ l4 ) .
Proof.
   simple induction l1.
    - intros l2 l3. custom27.
      -- intros a l3' Heq. right. exists a. exists l3'. auto.
      -- exists ( nil ( A := A ) ). auto.
    - clear l1intros a l1 Hrec l2 l3. custom25 l3 l4 H.
      -- custom13 a' l3' l4 Heq. custom9 Heq Heq' Heq''. elim Hrec with ( 1 := Heq' ).
        --- intros [ l1' [ Heq3 Heq4 ] ]. left. exists l1'. custom2 Heq'' Heq3.
        --- intros [ a'' [ l2' [ Heq3 Heq4 ] ] ]. right. exists a'', l2'. custom2 Heq'' Heq3.
      -- left. exists ( a :: l1 ). auto.
Qed.
Theorem length_app : forall { A : Type } ( l1 l2 : list A ), length ( l1 ++ l2 ) = length l1 + length l2 .
Proof.
   simple induction l1.
    - custom18.
    - custom18.
Qed.
Theorem length_rev : forall { A : Type } ( l : list A ), length l = length ( rev l ) .
Proof.
   simple induction l.
    - auto.
    - intros a l' H.
      -- simpl in.
      -- - *. rewrite length_app.
        --- simpl in.
        --- - *. rewrite <- plus_n_Sm. rewrite H. auto with arith.
Qed.
Theorem cons_to_app_end : forall { A : Type } ( l : list A ) ( a : A ), exists b : A, exists l' : list A, a :: l = l' ++ b :: nil .
Proof.
   intros A l a. rewrite <- ( rev_involutive ( a :: l ) ). destruct ( rev ( a :: l ) ) as [assert ( H : 0 < length ( rev ( a :: l ) ) ) by ( rewrite <- length_rev ; simpl ; auto with arith ) | a0 l0 ].
    - simpl. elim ( Nat.nlt_0_r 0 ). auto.
    - exists a0, ( rev l0 ). custom1.
Qed.
Theorem last_same : forall { A : Type } ( a b : A ) ( l1 l2 : list A ), l1 ++ a :: nil = l2 ++ b :: nil -> l1 = l2 /\ a = b .
Proof.
   intros A a b l1 l2 H. assert ( e : a :: rev l1 = b :: rev l2 ).
    - repeat rewrite <- rev_unit. now rewrite H.
    - custom9 e H1 H2. split.
      -- rewrite <- ( rev_involutive l1 ), H1. apply rev_involutive.
      -- auto.
Qed.
Theorem wp_remove_oc_aux : forall l : list par, wp l -> forall l1 l2 : list par, l1 ++ l2 = l -> wp ( l1 ++ open :: close :: l2 ) .
Proof.
   custom28 l H.
    - intros l1 l2 H1. elim ( app_eq_nil _ _ H1 ). custom8 Heq1 Heq2. rewrite Heq2. apply wp_oc.
    - intros l1 l2 Hp1 Hr1 Hp2 Hr2 l3 l4 Heq. elim app_decompose with ( 1 := Heq ).
      -- intros [ l1' [ Heq1 Heq2 ] ]. rewrite Heq1, <- app_assoc. custom10.
      -- intros [ a' [ l2' [ Heq1 Heq2 ] ] ]. rewrite Heq2. repeat rewrite app_comm_cons. custom11 app_assoc.
    - intros l' Hp'' Hrec l1. case l1.
      -- simpl. custom8 l2 Heq. change ( wp ( open :: nil ++ close :: open :: l' ++ close :: nil ) ). auto.
      -- custom19 c l1' l2. case l2.
        --- custom24 Heq. rewrite app_nil_r in Heq1. custom21 Heq1 Heq2. rewrite app_comm_cons. custom3 wp_concat. auto.
        --- intros c' l2'. elim ( cons_to_app_end l2' c' ). intros c'' [ l2'' Heq ]. custom21 Heq app_assoc. custom24 Heq1. elim last_same with ( 1 := Heq2 ). custom8 Heq4 Heq5. rewrite Heq3. change ( wp ( open :: l1' ++ ( open :: close :: l2'' ) ++ close :: nil ) ). custom16 app_assoc.
Qed.
Theorem wp_remove_oc : forall l1 l2 : list par, wp ( l1 ++ l2 ) -> wp ( l1 ++ open :: close :: l2 ) .
Proof.
   intros l1 l2 H. apply wp_remove_oc_aux with ( l := l1 ++ l2 ).
    - auto.
    - auto.
Qed.
Theorem make_list_end : forall ( A : Type ) ( a : A ) ( n : nat ) ( l : list A ), make_list A a ( S n ) ++ l = make_list A a n ++ a :: l .
Proof.
   simple induction n.
    - simpl. trivial.
    - custom19 n' H l. rewrite H. trivial.
Qed.
Theorem recognize_sound_aux : forall ( l : list par ) ( n : nat ), recognize n l = true -> wp ( make_list _ open n ++ l ) .
Proof.
   simple induction l.
    - custom12 n.
      -- simpl. intros H. apply wp_nil.
      -- custom29 n' H. custom12 a.
        --- clear aintros l' H n H0. custom22 make_list_end.
        --- clear aintros l' H n. case n.
          ---- intros H'. discriminate H'.
          ---- custom8 n H0 make_list_end. custom3 wp_remove_oc.
    - clear n.
Qed.
Theorem recognize_sound : forall l : list par, recognize 0 l = true -> wp l .
Proof.
   intros l H. generalize ( recognize_sound_aux _ _ H ). custom1.
Qed.
Theorem parse_reject_indep_t : forall ( l : list par ) ( s : list bin ) ( t : bin ), parse s t l = None -> forall ( s' : list bin ) ( t' : bin ), length s' = length s -> parse s' t' l = None .
Proof.
   custom20 a.
    - intros t0 s0 t H s'. custom5 s' t' Hle. custom1.
    - custom29 t H.
    - intros t H s' t' Hle. custom14 Hrec H.
    - case s'.
      -- custom1.
      -- custom13 t0 s0 t' Hle. discriminate Hle.
    - custom5 s' t' H0. custom13 t'0 s'0 t' Hle. apply Hrec with ( 1 := H ). auto with arith.
Qed.
Theorem parse_complete_aux : forall l : list par, wp' l -> forall ( s : list bin ) ( t : bin ) ( l' : list par ), parse s t ( l ++ l' ) = None -> forall ( s' : list bin ) ( t' : bin ), length s' = length s -> parse s' t' l' = None .
Proof.
   simple induction 1.
    - simpl. intros s t l' H0 s' t' H1. eapply parse_reject_indep_t.
      -- eauto.
      -- eauto.
    - intros l1 l2 Hp1 Hr1 Hp2 Hr2 s t l' Hrej s' t' Hle. apply Hr2 with ( s := s' ) ( t := N t L ).
      -- change ( parse ( t :: s' ) L ( close :: l2 ++ l' ) = None ) in.
      -- - *. simpl in Hrej. rewrite <- app_assoc in Hrej. custom14 Hr1 Hrej.
      -- .
Qed.
Theorem parse_complete : forall l : list par, wp l -> parse nil L l <> None .
Proof.
   intros l H. replace l with ( l ++ nil ).
    - red in.
    - - *. intros H'. assert ( e : parse nil L nil = None ).
      -- apply parse_complete_aux with ( 2 := H' ).
        --- custom3 wp_imp_wp'.
        --- auto.
      -- discriminate.
    - .
Qed.
Theorem parse_invert_aux : forall ( l : list par ) ( s : list bin ) ( t t' : bin ), parse s t l = Some t' -> bin_to_string' t' = unparse_stack s ++ bin_to_string' t ++ l .
Proof.
   custom20 a.
    - simpl. intros t0 s0 t t' H. discriminate H.
    - intros t t' H. injection H. intros Heq. rewrite Heq. now rewrite app_nil_r.
    - intros t t' H. custom4 Hrec H.
    - discriminate H.
    - custom4 Hrec Hp.
Qed.
Theorem parse_invert : forall ( l : list par ) ( t : bin ), parse nil L l = Some t -> bin_to_string' t = l .
Proof.
   intros l t H. replace l with ( unparse_stack nil ++ bin_to_string' L ++ l ).
    - custom3 parse_invert_aux.
    - auto.
Qed.
Theorem parse_sound : forall ( l : list par ) ( t : bin ), parse nil L l = Some t -> wp l .
Proof.
   intros l t H. rewrite <- parse_invert with ( 1 := H ). apply bin_to_string'_wp.
Qed.

Ltac custom0 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 :=  simple induction l; [intros H2; [case H2; [simpl |  | .. ] | .. ] | intros H3; [case H3; [clear H3simpl; [intros H4 H5 H6 | .. ] | simpl; [intros H7 H8 H9; [case H9; [intros H10 H11 H12 | intros H13 H14 H15 H16 H17 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom1  :=  simpl; [auto | .. ].
Ltac custom2 H5 H6 :=  split; [rewrite H5; [rewrite H6; [auto | .. ] | .. ] | auto | .. ].
Ltac custom3 H0 :=  apply H0; [auto | .. ].
Ltac custom4 H0 H1 :=  rewrite H0 with ( 1 := H1 ); [simpl; [repeat ( rewrite <- app_assoc ; simpl ); [auto | .. ] | .. ] | .. ].
Ltac custom5 H0 H1 H2 :=  case H0; [simpl; [intros H1 H2; [discriminate H2 | .. ] | .. ] |  | .. ].
Ltac custom6 H0 H1 :=  intros H0 H1; [elim H1; [auto | auto | .. ] | .. ].
Ltac custom7 H0 :=  apply H0; [trivial | .. ].
Ltac custom8 H0 H1 H2 :=  intros H0 H1; [rewrite H2 | .. ].
Ltac custom9 H0 H1 H2 :=  injection H0; [intros H1 H2 | .. ].
Ltac custom10  :=  custom3 ; [auto | .. ].
Ltac custom11 H0 :=  rewrite H0; [custom3 ; [auto | .. ] | .. ].
Ltac custom12 H0 :=  simpl; [intros H0; [case H0; [ |  | .. ] | .. ] | .. ].
Ltac custom13 H0 H1 H2 H3 :=  simpl; [intros H0 H1 H2 H3 | .. ].
Ltac custom14 H0 H1 :=  apply H0 with ( 1 := H1 ); [simpl; [auto with arith | .. ] | .. ].
Ltac custom15  :=  simple induction 1; [auto | auto |  | .. ].
Ltac custom16 H0 :=  rewrite H0; [auto | .. ].
Ltac custom17 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  elim H0; [ | intros H1 H2 H3 H4 H5 H6 H7 H8 | .. ].
Ltac custom18  :=  simpl in | - *; [auto | .. ].
Ltac custom19 H0 H1 H2 :=  simpl; [intros H0 H1 H2 | .. ].
Ltac custom20 H3 :=  custom0 ; [clear H3 |  |  |  |  | .. ].
Ltac custom21 H0 H1 :=  rewrite H0; [rewrite H1 | .. ].
Ltac custom22 H0 :=  rewrite <- H0; [auto | .. ].
Ltac custom23  :=  custom7 ; [trivial | .. ].
Ltac custom24 H0 :=  intros H0; [custom9  | .. ].
Ltac custom25 H0 H1 H2 :=  case H0; [intros H1 H2 |  | .. ].
Ltac custom26  :=  custom17 ; [custom1  |  | .. ].
Ltac custom27  :=  custom25 ; [ | left | .. ].
Ltac custom28 H0 H1 :=  intros H0 H1; [elim H1; [ |  |  | .. ] | .. ].
Ltac custom29 H0 H1 :=  intros H0 H1; [discriminate H1 | .. ].