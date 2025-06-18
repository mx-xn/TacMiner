Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.

Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.

Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.
Lemma immsafe_frame : forall h' c h, immsafe ( c, h ) -> hdisjoint h h' -> immsafe ( c, hunion h h' ) .
Proof.
   intros h' c h IMM. dependent induction IMM.
    - custom27 DISJ.
    - custom27 DISJ. auto.
    - custom27 DISJ.
    - intros DISJ. destruct ( isfinite ( hunion h h' ) ) as [ l' FIN ]. apply immsafe_alloc with ( Z.max 1 l' ).
      -- lia.
      -- custom48 i H1 FIN. lia.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom10 DISJ h l.
    - custom27 DISJ.
Qed.
Lemma red_frame : forall h2 c h1 c' h', red ( c, hunion h1 h2 ) ( c', h' ) -> immsafe ( c, h1 ) -> hdisjoint h1 h2 -> exists h1', red ( c, h1 ) ( c', h1' ) /\ hdisjoint h1' h2 /\ h' = hunion h1' h2 .
Proof.
   intros until h'. intros RED. dependent induction RED.
    - custom21 IMM DISJ h1. auto.
    - custom28 IMM DISJ h1.
    - custom30 IMM DISJ. edestruct IHRED as ( h1' & R & D & U ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom12 h1'. auto.
    - custom30 IMM DISJ. custom12 h1.
    - custom30 IMM DISJ. exists ( hinit l sz h1 ). custom49.
      -- intros i H1. apply H in H1. cbn in H1. destruct ( h1 i ) as [ z| ].
        --- congruence.
        --- congruence.
      -- auto.
      -- red. intros i. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- right. destruct ( h1 i ) as [ z| ], ( h2 i ) as [ z'| ].
          ---- congruence.
          ---- congruence.
          ---- congruence.
          ---- congruence.
        --- rewrite hinit_outside by auto. apply DISJ.
      -- custom2 heap_extensionality i. cbn. assert ( EITHER : l <= i < l + Z.of_nat sz \/ ( i < l \/ l + Z.of_nat sz <= i ) ) by lia. destruct EITHER as [  H1 | H1 ].
        --- custom43 hinit_inside.
        --- custom43 hinit_outside.
    - apply H in H1. cbn in H1. custom30 IMM DISJ. custom12 h1. cbn in H. destruct ( h1 l ) as [ z| ].
      -- congruence.
      -- congruence.
    - intros IMM DISJ. exists ( hupdate l v h1 ). custom1 IMM i heap_extensionality DISJ i l.
      -- intuition congruence.
      -- auto.
    - custom30 IMM DISJ. exists ( hfree l h1 ). custom49.
      -- auto.
      -- custom41 i. generalize ( DISJ i ). destruct ( Z.eq_dec l i ) as [  e | n ].
        --- intuition congruence.
        --- intuition congruence.
      -- custom2 heap_extensionality i. custom23 l i. subst i. generalize ( DISJ l ). intuition.
Qed.
Lemma safe_frame : forall ( R : assertion ) h', R h' -> forall c h Q, safe c h Q -> hdisjoint h h' -> safe c ( hunion h h' ) ( fun v => Q v ** R ) .
Proof.
   induction 2.
    - custom27 DISJ. exists h, h'. auto.
    - custom27 DISJ.
      -- auto.
      -- custom25 immsafe_frame.
      -- intros c' h'0 H4. edestruct red_frame as ( h1' & RED1 & D & U ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- custom37 h'0 H3.
Qed.
Lemma triple_frame : forall P c Q R, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   intros P c Q R TR h ( h1 & h2 & P1 & R2 & D & U ). custom37 h safe_frame. auto.
Qed.
Lemma triple_get : forall l v, ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros l v h P. custom9 h l v c' h' RED hupdate_same. split.
    - congruence.
    - auto.
Qed.
Lemma triple_set : forall l v, ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros l v h ( v0 & P ). custom9 h l v0 c' h' RED hupdate_same. red in P. red in P. subst h. custom13 heap_extensionality l' l.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom41 l. custom16.
    - custom41 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). intuition auto.
      -- exists 0. custom16.
      -- intros x. unfold hupdate, hempty. custom23 l x. right. rewrite hinit_outside by lia. auto.
      -- custom2 heap_extensionality x. custom23 l x. auto.
Qed.
Lemma triple_alloc : forall sz, ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros sz h P. red in P. subst h. constructor.
    - auto.
    - apply immsafe_alloc with 1.
      -- lia.
      -- intros i H. auto.
    - intros c' h' RED. custom46 RED. split.
      -- auto.
      -- apply valid_N_init.
Qed.
Lemma triple_free : forall l, ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros l h ( v0 & P ). red in P. custom9 h l v0 c' h' RED hupdate_same. custom13 heap_extensionality x l.
Qed.

Lemma safe_pure : forall v h Q, safe ( PURE v ) h Q -> Q v h .
Proof.
   intros v h Q H. inv H.
    - auto.
    - contradiction.
Qed.
Lemma safe_red : forall c h Q c' h', safe c h Q -> red ( c, h ) ( c', h' ) -> safe c' h' Q .
Proof.
   intros c h Q c' h' H H0. inv H.
    - inv H0.
    - eauto.
Qed.
Lemma safe_immsafe : forall c h Q, safe c h Q -> immsafe ( c, h ) .
Proof.
   intros c h Q H. custom46 H. auto.
Qed.
Lemma safe_let : forall ( Q R : postcond ) f, ( forall v h', Q v h' -> safe ( f v ) h' R ) -> forall c h, safe c h Q -> safe ( LET c f ) h R .
Proof.
   intros Q R f POST. induction 1.
    - custom0 c' h' RED.
      -- constructor.
      -- custom3 POST.
      -- inv H1.
    - custom0 c' h' RED.
      -- auto.
      -- contradiction.
      -- eauto.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ), ( forall v, Q v -->> Q' v ) -> forall c h, safe c h Q -> safe c h Q' .
Proof.
   intros Q Q' IMP. induction 1.
    - custom7 safe_done IMP. assumption.
    - custom25 safe_step. auto.
Qed.
Lemma triple_pure : forall P v ( Q : postcond ), P -->> Q v -> ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma triple_let : forall c f ( P : precond ) ( Q R : postcond ), ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma triple_ifthenelse : forall b c1 c2 P Q, ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma triple_consequence : forall P P' c Q' Q, ⦃ P' ⦄ c ⦃ Q' ⦄ -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma triple_pick : forall n, ⦃ emp ⦄ PICK n ⦃ fun i => pure ( 0 <= i < n ) ⦄ .
Proof.
   intros n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_consequence_pre : forall P P' c Q, ⦃ P' ⦄ c ⦃ Q ⦄ -> P -->> P' -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H H0. custom45 triple_consequence P' Q.
    - auto.
    - intros v. custom16.
Qed.
Lemma triple_consequence_post : forall P c Q Q', ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, Q' v -->> Q v ) -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q Q' H H0. custom45 triple_consequence P Q'.
    - custom16.
    - auto.
Qed.
Lemma triple_lift_pure : forall ( P : Prop ) P' c Q, ( P -> ⦃ P' ⦄ c ⦃ Q ⦄ ) -> ⦃ P //\\ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' c Q H. intros h [ P1 P2 ]. custom25 H.
Qed.
Lemma triple_lift_exists : forall ( X : Type ) ( P : X -> assertion ) c Q, ( forall x, ⦃ P x ⦄ c ⦃ Q ⦄ ) -> ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   intros X P c Q H. intros h ( x & Px ). apply ( H x ). auto.
Qed.
Lemma triple_ifthen : forall b c1 c2 P Q, b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - auto.
    - lia.
Qed.
Lemma triple_ifelse : forall b c1 c2 P Q, b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ -> ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros b c1 c2 P Q H H0. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - lia.
    - auto.
Qed.
Lemma unroll_com : forall c, c = match c with | PURE x => PURE x | LET c f => LET c f | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2 | ALLOC sz => ALLOC sz | GET l => GET l | SET l v => SET l v | FREE l => FREE l | PICK n => PICK n end .
Proof.
   destruct c as [  x | f c | c2 c1 b | sz | l | v l | l | n ].
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
Qed.
Lemma list_cons_correct : forall a n l, ⦃ list_at a l ⦄ list_cons n a ⦃ fun a' => list_at a' ( n :: l ) ⦄ .
Proof.
   intros a n l. custom34 triple_let b.
    - rewrite <- sepconj_emp at 1. custom7 triple_frame triple_alloc.
    - rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. custom2 triple_lift_pure H1. custom19 triple_let.
      -- custom7 triple_frame triple_set.
      -- custom19 triple_let.
        --- custom44 sepconj_pick2 triple_frame triple_set.
        --- rewrite sepconj_pick2. custom32 triple_pure h A a.
Qed.
Lemma list_length_rec_correct : forall l a len, ⦃ list_at a l ⦄ list_length_rec a len ⦃ fun len' => ( len' = len + Z.of_nat ( List.length l ) ) //\\ list_at a l ⦄ .
Proof.
   intro l. induction l as [ | h t ].
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom3 triple_ifelse. apply triple_pure. intros h H2. split.
      -- lia.
      -- custom14.
    - custom22 a len unroll_com list_length_rec triple_lift_pure H1. custom40 triple_lift_exists a' triple_ifthen. eapply triple_let.
      -- custom44 sepconj_pick2 triple_frame triple_get.
      -- simpl. intros a''. rewrite lift_pureconj. custom2 triple_lift_pure H3. subst a''. rewrite sepconj_swap3. custom34 triple_consequence_post len'.
        --- custom7 triple_frame IHt.
        --- rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 ( A & B ). split.
          ---- lia.
          ---- custom8 a'.
Qed.
Corollary list_length_correct : forall l a, ⦃ list_at a l ⦄ list_length a ⦃ fun len => ( len = Z.of_nat ( length l ) ) //\\ list_at a l ⦄ .
Proof.
   custom48 l a list_length_rec_correct.
Qed.
Lemma list_concat_rec_correct : forall l2 a2 l1 a1, a1 <> 0 -> ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat_rec a1 a2 ⦃ fun _ => list_at a1 ( l1 ++ l2 ) ⦄ .
Proof.
   intros l2 a2 l1. induction l1 as [ | h1 t1 ].
    - intros a1 H. rewrite ( unroll_com ( list_concat_rec a1 a2 ) ). custom42 lift_pureconj triple_lift_pure H0.
    - intros a1 H. custom31 unroll_com list_concat_rec a1 a2 lift_pureconj triple_lift_pure H1 lift_aexists. custom2 triple_lift_exists a'. rewrite sepconj_assoc. custom24 triple_let t lift_pureconj triple_lift_pure H2.
      -- rewrite sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom18 triple_ifthenelse triple_lift_pure H2 H2.
        --- rewrite <- sepconj_assoc, sepconj_comm. custom19 triple_consequence_post.
          ---- apply triple_frame. custom3 IHt1.
          ---- rewrite sepconj_pick2, sepconj_swap3. intros h P. custom8 a'.
        --- custom6 triple_consequence_post triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. destruct t1 as [  IHt1 | IHt1 z ].
          ---- simpl. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). custom8 a2.
          ---- simpl. rewrite lift_pureconj. intros h ( A & B ). lia.
Qed.
Lemma list_concat_correct : forall l1 a1 l2 a2, ⦃ list_at a1 l1 ** list_at a2 l2 ⦄ list_concat a1 a2 ⦃ fun a => list_at a ( l1 ++ l2 ) ⦄ .
Proof.
   intros l1 a1 l2 a2. unfold list_concat. custom18 triple_ifthenelse triple_lift_pure H1 H1.
    - custom19 triple_let.
      -- custom3 list_concat_rec_correct.
      -- custom47 triple_pure.
    - destruct l1 as [  | z ].
      -- simpl. apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h ( A & B ). auto.
      -- custom42 lift_pureconj triple_lift_pure H.
Qed.
Lemma list_rev_rec_correct : forall l a l' p, ⦃ list_at a l ** list_at p l' ⦄ list_rev_rec a p ⦃ fun x => list_at x ( List.rev_append l l' ) ⦄ .
Proof.
   intro l. induction l as [ | hd l ].
    - intros a l' p. rewrite ( unroll_com ( list_rev_rec a p ) ). simpl. rewrite lift_pureconj, sepconj_emp. custom40 triple_lift_pure H1 triple_ifelse. custom47 triple_pure.
    - intros a l' p. custom31 unroll_com list_rev_rec a p lift_pureconj triple_lift_pure H1 lift_aexists. custom40 triple_lift_exists a' triple_ifthen. custom24 triple_let a'' lift_pureconj triple_lift_pure H3.
      -- rewrite ! sepconj_assoc, sepconj_pick2. custom7 triple_frame triple_get.
      -- custom6 triple_let triple_frame triple_consequence_pre triple_set h P sepconj_pick2 sepconj_pick3 a'. custom33 triple_consequence_pre IHl. custom32 sepconj_imp_r h A p.
Qed.
Lemma list_rev_correct : forall a l, ⦃ list_at a l ⦄ list_rev a ⦃ fun x => list_at x ( List.rev l ) ⦄ .
Proof.
   intros a l. rewrite List.rev_alt. custom33 triple_consequence_pre list_rev_rec_correct. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A. custom14.
Qed.
Lemma Hoare_pure : forall P v ( Q : postcond ), P -->> Q v -> Hoare P ( PURE v ) Q .
Proof.
   custom29 P v Q H h Ph.
Qed.
Lemma Hoare_let : forall c f ( P : precond ) ( Q R : postcond ), Hoare P c Q -> ( forall v, Hoare ( Q v ) ( f v ) R ) -> Hoare P ( LET c f ) R .
Proof.
   custom20 R HR1 HR2 h Ph safe_let Q.
Qed.
Lemma Hoare_ifthenelse : forall b c1 c2 P Q, Hoare ( ( b <> 0 ) //\\ P ) c1 Q -> Hoare ( ( b = 0 ) //\\ P ) c2 Q -> Hoare P ( IFTHENELSE b c1 c2 ) Q .
Proof.
   custom4 Q HR1 HR2 h Ph c' h' RED b.
Qed.
Lemma Hoare_consequence : forall P P' c Q' Q, Hoare P' c Q' -> P -->> P' -> ( forall v, Q' v -->> Q v ) -> Hoare P c Q .
Proof.
   custom15 P P' c Q' Q H H0 H1 h H2 safe_consequence.
Qed.
Lemma Hoare_pick : forall P n, Hoare P ( PICK n ) ( fun i => ( 0 <= i < n ) //\\ P ) .
Proof.
   intros P n h Ph. custom36 c' h' RED.
Qed.
Lemma triple_frame_consequence : forall R P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** R -> ( forall v, Q v ** R -->> Q' v ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros R P c Q P' Q' H H0 H1. apply triple_consequence with ( P ** R ) ( fun v => Q v ** R ).
    - custom3 triple_frame.
    - auto.
    - auto.
Qed.
Lemma triple_ramification : forall P c Q P' Q', ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P ** ( aforall ( fun v => Q v --* Q' v ) ) -> ⦃ P' ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P c Q P' Q' H H0. eapply triple_frame_consequence with ( R := aforall ( fun v => Q v --* Q' v ) ).
    - eassumption.
    - assumption.
    - custom26 v h h1 h2 Q1 W2 D U wand_cancel Q.
Qed.
Lemma wp_precond : forall c Q, ⦃ wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h ( P & T & C ). custom3 T.
Qed.
Lemma wp_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp c Q .
Proof.
   intros P c Q T h Ph. exists P. custom14.
Qed.
Corollary wp_equiv : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ <-> ( P -->> wp c Q ) .
Proof.
   intros P c Q. split.
    - intros H. custom3 wp_weakest.
    - intros H. apply triple_consequence_pre with ( wp c Q ).
      -- auto using wp_precond.
      -- auto using wp_precond.
Qed.
Lemma wp'_precond : forall c Q, ⦃ wp' c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intros c Q h SAFE. apply SAFE.
Qed.
Lemma wp'_weakest : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> P -->> wp' c Q .
Proof.
   intros P c Q H. intros h Ph. custom3 H.
Qed.
Lemma wp_consequence : forall ( Q Q' : postcond ) c, ( forall v, Q v -->> Q' v ) -> wp c Q -->> wp c Q' .
Proof.
   intros Q Q' c H. apply wp_weakest. apply triple_consequence_post with Q.
    - auto using wp_precond.
    - auto using wp_precond.
Qed.
Lemma wp_frame : forall R c Q, wp c Q ** R -->> wp c ( fun v => Q v ** R ) .
Proof.
   intros R c Q. custom7 wp_weakest triple_frame. apply wp_precond.
Qed.
Corollary wp_frame_consequence : forall R Q c Q', ( forall v, Q v ** R -->> Q' v ) -> wp c Q ** R -->> wp c Q' .
Proof.
   intros R Q c Q' H. custom38 h H0. apply wp_consequence with ( fun v => Q v ** R ).
    - assumption.
    - custom3 wp_frame.
Qed.
Corollary wp_ramification : forall c Q Q', wp c Q ** aforall ( fun v => Q v --* Q' v ) -->> wp c Q' .
Proof.
   custom50 c Q Q' wp_frame_consequence. custom26 v h h1 h2 A B D U wand_cancel Q.
Qed.
Lemma wp_pure : forall ( Q : postcond ) v, Q v -->> wp ( PURE v ) Q .
Proof.
   intros Q v. custom7 wp_weakest triple_pure. custom16.
Qed.
Lemma wp_let : forall c f Q, wp c ( fun v => wp ( f v ) Q ) -->> wp ( LET c f ) Q .
Proof.
   custom50 c f Q wp_weakest. eapply triple_let.
    - apply wp_precond.
    - intros v. apply wp_precond.
Qed.
Lemma wp_ifthenelse : forall b c1 c2 Q, ( if b =? 0 then wp c2 Q else wp c1 Q ) -->> wp ( IFTHENELSE b c1 c2 ) Q .
Proof.
   intros b c1 c2 Q. custom7 wp_weakest triple_ifthenelse.
    - custom35 triple_consequence_pre wp c1 Q wp_precond h A B. rewrite <- Z.eqb_neq in A. rewrite A in B. auto.
    - custom35 triple_consequence_pre wp c2 Q wp_precond h A B. subst b. auto.
Qed.
Lemma wp_alloc : forall sz Q, aforall ( fun l => ( l <> 0 ) //\\ valid_N l sz --* Q l ) -->> wp ( ALLOC sz ) Q .
Proof.
   intros sz Q. custom38 h H. apply wp_ramification with ( Q := fun l => ( l <> 0 ) //\\ valid_N l sz ). apply sepconj_imp_l with emp.
    - custom7 wp_weakest triple_alloc.
    - rewrite sepconj_emp. assumption.
Qed.
Lemma wp_get : forall l v Q, contains l v ** ( contains l v --* Q v ) -->> wp ( GET l ) Q .
Proof.
   intros l v Q. assert ( W : contains l v -->> wp ( GET l ) ( fun v' => ( v' = v ) //\\ contains l v ) ).
    - custom7 wp_weakest triple_get.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. intros h' H' v' h'' D ( A & B ). custom37 v' H'.
Qed.
Lemma wp_set : forall l v Q, valid l ** aforall ( fun v' => ( contains l v --* Q v' ) ) -->> wp ( SET l v ) Q .
Proof.
   intros l v Q. assert ( W : valid l -->> wp ( SET l v ) ( fun _ => contains l v ) ).
    - custom7 wp_weakest triple_set.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom16.
Qed.
Corollary wp_set' : forall l v Q, valid l ** ( contains l v --* Q ) -->> wp ( SET l v ) ( fun _ => Q ) .
Proof.
   intros l v Q. custom17 h H wp_set sepconj_imp_r. instantiate ( 1 := contains l v --* Q ). custom51 h' H' v'.
Qed.
Lemma wp_free : forall l Q, valid l ** aforall ( fun v' => Q v' ) -->> wp ( FREE l ) Q .
Proof.
   intros l Q. assert ( W : valid l -->> wp ( FREE l ) ( fun _ => emp ) ).
    - custom7 wp_weakest triple_free.
    - custom39 h H wp_ramification sepconj_imp_l W sepconj_imp_r. custom38 h0 H0. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0.
Qed.
Corollary wp_free' : forall l Q, valid l ** Q -->> wp ( FREE l ) ( fun _ => Q ) .
Proof.
   intros l Q. custom17 h H wp_free sepconj_imp_r. instantiate ( 1 := Q ). custom51 h' H' v'.
Qed.
Lemma wp_pick : forall n Q, aforall ( fun i => pure ( 0 <= i < n ) --* Q i ) -->> wp ( PICK n ) Q .
Proof.
   intros n Q. assert ( W : emp -->> wp ( PICK n ) ( fun i => pure ( 0 <= i < n ) ) ).
    - custom7 wp_weakest triple_pick.
    - custom5 h H wp_ramification sepconj_imp_l W sepconj_imp_r.
      -- custom16.
      -- rewrite sepconj_emp. eexact H.
Qed.

Ltac custom0 H0 H1 H2 :=  constructor; [auto | constructor | intros H0 H1 H2; [inv H2 | .. ] | .. ].
Ltac custom1 H0 H14 H15 H2 H16 H7 :=  inv H0; [intuition auto; [constructor; [auto | .. ] | intros H14; [cbn; [generalize ( H2 H14 ); [destruct ( Z.eq_dec H7 H14 ); [ | intuition congruence | .. ] | .. ] | .. ] | .. ] | apply H15; [intros H16; [cbn; [destruct ( Z.eq_dec H7 H16 ); [ | auto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom2 H0 H1 :=  apply H0; [intros H1 | .. ].
Ltac custom3 H0 :=  apply H0; [auto | .. ].
Ltac custom4 H0 H5 H6 H7 H8 H9 H10 H11 H4 :=  intros until H0; [intros H5 H6 H7 H8; [custom0 H9 H10 H11; [destruct ( Z.eqb_spec H4 0 ); [apply H6; [split; [auto | auto | .. ] | .. ] | apply H5; [split; [auto | auto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom5 H0 H1 H2 H3 H4 H5 :=  red; [intros H0 H1; [eapply H2; [eapply H3; [eexact H4 | eapply H5 | .. ] | .. ] | .. ] | .. ].
Ltac custom6 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  eapply H0; [apply H1; [eapply H2; [apply H3 | intros H4 H5; [exists H8; [auto | .. ] | .. ] | .. ] | .. ] | simpl; [intros _; [rewrite H6, H7 | .. ] | .. ] | .. ].
Ltac custom7 H0 H1 :=  apply H0; [apply H1 | .. ].
Ltac custom8 H2 :=  split; [auto | exists H2; [auto | .. ] | .. ].
Ltac custom9 H0 H1 H2 H5 H6 H7 H12 :=  assert ( L : H0 H1 = Some H2 ); [subst H0; [apply H12 | .. ] | custom0 H5 H6 H7; [congruence | constructor | .. ] | .. ].
Ltac custom10 H0 H1 H2 :=  intros H0; [constructor; [cbn; [destruct ( H1 H2 ) as [ z| ]; [congruence | congruence | .. ] | .. ] | .. ] | .. ].
Ltac custom11 H0 H1 H2 :=  simpl; [rewrite H0; [custom2 H1 H2 | .. ] | .. ].
Ltac custom12 H0 :=  exists H0; [intuition auto; [constructor | .. ] | .. ].
Ltac custom13 H0 H1 H2 :=  red; [custom2 H0 H1; [cbn; [destruct ( Z.eq_dec H2 H1 ); [auto | auto | .. ] | .. ] | .. ] | .. ].
Ltac custom14  :=  split; [auto | auto | .. ].
Ltac custom15 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 :=  intros H0 H1 H2 H3 H4 H5 H6 H7; [red; [intros H8 H9; [apply H10 with H3; [auto | auto | .. ] | .. ] | .. ] | .. ].
Ltac custom16  :=  red; [auto | .. ].
Ltac custom17 H0 H1 H2 H3 :=  red; [intros H0 H1; [apply H2; [eapply H3; [ | eauto | .. ] | .. ] | .. ] | .. ].
Ltac custom18 H0 H1 H2 H3 :=  apply H0; [custom2 H1 H2 | custom2 H1 H3 | .. ].
Ltac custom19 H0 :=  eapply H0; [ | simpl; [intros _ | .. ] | .. ].
Ltac custom20 H0 H5 H6 H7 H8 H9 H1 :=  intros until H0; [intros H5 H6 H7 H8; [apply H9 with H1; [apply H6 | custom3 H5 | .. ] | .. ] | .. ].
Ltac custom21 H0 H1 H2 :=  intros H0 H1; [custom12 H2; [inv H0 | .. ] | .. ].
Ltac custom22 H0 H1 H2 H3 H4 H5 :=  intros H0 H1; [rewrite ( H2 ( H3 H0 H1 ) ); [cbn; [apply H4; [intro H5 | .. ] | .. ] | .. ] | .. ].
Ltac custom23 H0 H1 :=  cbn; [destruct ( Z.eq_dec H0 H1 ); [ | auto | .. ] | .. ].
Ltac custom24 H0 H1 H2 H3 H4 :=  eapply H0; [ | intros H1; [custom11 H2 H3 H4; [subst H1 | .. ] | .. ] | .. ].
Ltac custom25 H0 :=  custom3 H0; [auto | .. ].
Ltac custom26 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 :=  intros H0 H1 ( H2 & H3 & H4 & H5 & H6 & H7 ); [apply ( H8 ( H9 H0 ) ); [exists H2, H3; [auto | .. ] | .. ] | .. ].
Ltac custom27 H0 :=  intros H0; [constructor | .. ].
Ltac custom28 H0 H1 H2 :=  intros H0 H1; [custom12 H2 | .. ]. inv H0.
Ltac custom29 H0 H1 H2 H3 H4 H5 :=  intros H0 H1 H2 H3; [intros H4 H5; [constructor; [custom3 H3 | .. ] | .. ] | .. ].
Ltac custom30 H0 H1 :=  intros H0 H1; [inv H0 | .. ].
Ltac custom31 H0 H1 H2 H3 H4 H5 H6 H7 :=  rewrite ( H0 ( H1 H2 H3 ) ); [custom11 H4 H5 H6; [rewrite H7 | .. ] | .. ].
Ltac custom32 H0 H1 H2 H3 :=  apply H0; [intros H1 H2; [custom8 H3 | .. ] | .. ].
Ltac custom33 H0 H1 :=  eapply H0; [apply H1 | simpl | .. ].
Ltac custom34 H0 H1 :=  eapply H0; [ | intros H1; [simpl | .. ] | .. ].
Ltac custom35 H0 H1 H2 H3 H4 H5 H6 H7 :=  apply H0 with ( H1 H2 H3 ); [apply H4 | intros H5 ( H6 & H7 ) | .. ].
Ltac custom36 H0 H1 H2 :=  custom0 H0 H1 H2; [constructor; [custom14  | .. ] | .. ].
Ltac custom37 H0 H5 :=  subst H0; [custom25 H5 | .. ].
Ltac custom38 H0 H1 :=  red; [intros H0 H1 | .. ].
Ltac custom39 H4 H5 H0 H1 H2 H3 :=  custom5 H4 H5 H0 H1 H2 H3; [ | eexact H5 | .. ].
Ltac custom40 H0 H1 H2 :=  custom2 H0 H1; [custom3 H2 | .. ].
Ltac custom41 H0 :=  intros H0; [cbn | .. ].
Ltac custom42 H0 H1 H2 :=  custom11 H0 H1 H2; [lia | .. ].
Ltac custom43 H0 :=  rewrite ! H0 by auto; [auto | .. ].
Ltac custom44 H0 H1 H2 :=  rewrite H0; [custom7 H1 H2 | .. ].
Ltac custom45 H0 H1 H2 :=  apply H0 with H1 H2; [auto | .. ].
Ltac custom46 H0 :=  inv H0; [constructor | .. ].
Ltac custom47 H0 :=  apply H0; [custom16  | .. ].
Ltac custom48 H0 H1 H2 :=  intros H0 H1; [apply H2 | .. ].
Ltac custom49  :=  intuition auto; [constructor | .. ].
Ltac custom50 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3 | .. ].
Ltac custom51 H0 H1 H2 :=  intros H0 H1 H2; [auto | .. ].
