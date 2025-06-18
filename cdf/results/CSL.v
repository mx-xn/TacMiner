Lemma safe_pure : forall n v h ( Q : postcond ) J, Q v h -> safe n ( PURE v ) h Q J .
Proof.
   intros n v h Q J H. custom35 n. constructor. auto.
Qed.
Lemma safe_pure_inv : forall n v h Q J, safe ( S n ) ( PURE v ) h Q J -> Q v h .
Proof.
   intros n v h Q J H. custom76 H. auto.
Qed.
Lemma safe_red : forall n c h1 Q J hj hf c' h', red ( c, hunion h1 ( hunion hj hf ) ) ( c', h' ) -> safe ( S n ) c h1 Q J -> J hj -> hdisj3 h1 hj hf -> exists h1' hj', hdisj3 h1' hj' hf /\ h' = hunion h1' ( hunion hj' hf ) /\ J hj' /\ safe n c' h1' Q J .
Proof.
   intros n c h1 Q J hj hf c' h' H H0 H1 H2. inv H0.
    - inv H.
    - eauto.
Qed.
Lemma safe_redN : forall n c h1 Q J hj hf c' h', starN red n ( c, hunion h1 ( hunion hj hf ) ) ( c', h' ) -> safe ( S n ) c h1 Q J -> J hj -> hdisj3 h1 hj hf -> exists h1' hj', hdisj3 h1' hj' hf /\ h' = hunion h1' ( hunion hj' hf ) /\ J hj' /\ safe 1 % nat c' h1' Q J .
Proof.
   custom55 n.
    - intros c h1 Q J hj hf c' h' H H0 H1 H2. inv H. custom38 h1 hj.
    - intros c h1 Q J hj hf c' h' H H0 H1 H2. inv H. rename c' into c''. rename h' into h''. destruct b as [ c' h' ]. edestruct safe_red as ( h1' & hj' & A & B & C & D ).
      -- eassumption.
      -- eassumption.
      -- assumption.
      -- assumption.
      -- subst h'. custom45 IHn.
        --- eauto.
        --- eauto.
Qed.
Lemma safe_not_erroneous : forall n c h1 Q J hj hf, safe ( S n ) c h1 Q J -> hdisj3 h1 hj hf -> J hj -> ~ erroneous ( c, hunion h1 ( hunion hj hf ) ) .
Proof.
   intros n c h1 Q J hj hf H H0 H1. inv H.
    - custom72 ST.
    - eauto.
Qed.
Lemma safe_immacc : forall n c h1 Q J l, safe ( S n ) c h1 Q J -> immacc l c -> h1 l <> None .
Proof.
   intros n c h1 Q J l H H0. custom77 H. eapply ACC. auto.
Qed.
Lemma safe_mono : forall n c h Q J, safe n c h Q J -> forall n', ( n' <= n ) % nat -> safe n' c h Q J .
Proof.
   custom55 n.
    - intros c h Q J H n' H0. replace n' with O by lia. constructor.
    - intros c h Q J H n' H0. destruct n' as [ | n' ].
      -- constructor.
      -- custom3 H hf hj h0 c' h' H H1 H2 H3 STEP h1' hj'. intuition auto. custom7 IHn. lia.
Qed.
Lemma safe_frame : forall ( R : assertion ) ( Q : postcond ) J n c h h', safe n c h Q J -> hdisjoint h h' -> R h' -> safe n c ( hunion h h' ) ( fun v => Q v ** R ) J .
Proof.
   custom1 R Q J n c h h' H H0 H1 c h h' H H0 H1 hf hj h0 c' h'0 H H2 H3 H4 l H hf hj h0 H H2 H3 ACC.
    - subst h0. custom50 IMM hunion h' hf hj. rewrite hunion_assoc. f_equal. rewrite hunion_comm by HDISJ. rewrite hunion_assoc. f_equal. apply hunion_comm. HDISJ.
    - subst h0. edestruct ( STEP ( hunion h' hf ) hj ) as ( h1' & hj' & A & B & C & D ).
      -- HDISJ.
      -- eauto.
      -- eauto.
      -- rewrite ( hunion_comm ( hunion h' hf ) ) by HDISJ. rewrite hunion_assoc. rewrite <- hunion_assoc. rewrite ( hunion_comm hj ) by HDISJ. eauto.
      -- custom27 h1' h' hj' IHn.
        --- rewrite hunion_assoc. rewrite ( hunion_comm ( hunion hj' hf ) ) by HDISJ. rewrite hunion_assoc. rewrite ( hunion_comm h' ) by HDISJ. assumption.
        --- assumption.
Qed.
Lemma triple_frame : forall J P c Q R, J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ .
Proof.
   custom79 J P c Q R H n h H0. destruct H0 as ( h1 & h2 & P1 & R2 & D & U ). custom19 h safe_frame.
Qed.

Lemma safe_frame_invariant : forall Q ( J J' : invariant ) n c h, safe n c h Q J -> safe n c h Q ( J ** J' ) .
Proof.
   intros Q J J' n. custom17 n c h H c h H.
    - auto.
    - custom2 hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1.
      -- auto.
      -- destruct H1 as ( hj1 & hj2 & A & B & C & D ). subst hj h0. custom50 IMM hunion hj2 hf hj1. custom43 hunion_assoc.
      -- destruct H1 as ( hj1 & hj2 & A & B & C & D ). subst hj h0. edestruct ( STEP ( hunion hj2 hf ) hj1 ) as ( h1' & hj1' & U & V & X & Y ).
        --- HDISJ.
        --- eauto.
        --- auto.
        --- rewrite <- ( hunion_assoc hj1 ) by HDISJ. eauto.
        --- subst h'. exists h1', ( hunion hj1' hj2 ). custom4 IHn.
          ---- custom43 hunion_assoc.
          ---- custom36 hj1' hj2.
Qed.
Lemma triple_frame_invariant : forall J J' P c Q, J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ** J' ⊢ ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   custom79 J J' P c Q H n h H0. custom7 safe_frame_invariant.
Qed.
Lemma triple_atomic : forall J P c ( Q : postcond ), emp ⊢ ⦃ P ** J ⦄ c ⦃ fun v => Q v ** J ⦄ -> J ⊢ ⦃ P ⦄ ATOMIC c ⦃ Q ⦄ .
Proof.
   intros until Q. intros TR n h Ph. custom25 n hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1 ST.
    - custom8 STEPS TR h hj. custom61.
      -- eexact D.
      -- eexact A.
      -- auto.
    - custom34 ST star_starN H4 H4 hunion_assoc STEPS. rewrite <- ( hunion_empty hf ) in STEPS. subst h'. inv H2. apply star_starN in H4. destruct H4 as ( N & STEPS ). rewrite <- hunion_assoc in STEPS. rewrite <- ( hunion_empty hf ) in STEPS. edestruct safe_redN as ( h1' & hj' & A & B & C & D ).
      -- eexact STEPS.
      -- apply TR. custom36 h hj.
      -- reflexivity.
      -- HDISJ.
      -- subst h'. apply safe_pure_inv in D. destruct D as ( h1'' & hj'' & U & V & X & Y ). subst h1'. exists h1'', hj''. custom4 safe_pure.
        --- rewrite hunion_assoc. rewrite C. rewrite hunion_empty. auto.
        --- auto.
Qed.
Lemma safe_share : forall Q ( J J' : invariant ) n c h h', safe n c h Q ( J ** J' ) -> hdisjoint h h' -> J' h' -> safe n c ( hunion h h' ) ( fun v => Q v ** J' ) J .
Proof.
   intros Q J J' n. induction n.
    - intros c h h' H H0 H1. constructor.
    - intros c h h' H H0 H1. inv H.
      -- constructor. custom38 h h'.
      -- custom2 hf hj h0 c' h'0 H H2 H3 H4 hf hj h0 H H2 H3.
        --- intros l H. apply ACC in H. cbn. custom48 h l.
        --- apply ( IMM hf ( hunion h' hj ) ).
          ---- HDISJ.
          ---- custom51 h0 hunion_assoc.
          ---- custom62 hunion_comm hj h'.
        --- edestruct ( STEP hf ( hunion h' hj ) ) as ( h1' & hj' & U & V & X & Y ).
          ---- HDISJ.
          ---- custom51 h0 hunion_assoc.
          ---- custom62 hunion_comm hj h'.
          ---- rewrite <- hunion_assoc by HDISJ. subst h0. eauto.
          ---- destruct X as ( hj1' & hj2' & A & B & C & D ). subst hj' h'0 h0. custom27 h1' hj2' hj1' IHn.
            ----- rewrite ( hunion_comm hj2' ) by HDISJ. rewrite ! hunion_assoc. auto.
            ----- auto.
Qed.
Lemma triple_share : forall J J' P c Q, J ** J' ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P ** J' ⦄ c ⦃ fun v => Q v ** J' ⦄ .
Proof.
   intros J J' P c Q H. intros n h ( h1 & h2 & Ph1 & J'h2 & D & U ). custom19 h safe_share.
Qed.
Lemma triple_pure : forall J P Q v, aimp P ( Q v ) -> J ⊢ ⦃ P ⦄ PURE v ⦃ Q ⦄ .
Proof.
   intros J P Q v IMP n h Ph. custom7 safe_pure.
Qed.
Lemma safe_let : forall ( Q R : postcond ) ( J : invariant ) f n c h, safe n c h Q J -> ( forall v n' h', Q v h' -> ( n' < n ) % nat -> safe n' ( f v ) h' R J ) -> safe n ( LET c f ) h R J .
Proof.
   intros Q R J f n. custom71 n h.
    - custom75 S1 S2.
    - intros until h. intros S1 S2. custom2 hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1.
      -- intros l H. custom45 safe_immacc.
      -- red. intros H2. inv H2. custom61.
        --- eauto.
        --- eauto.
        --- eauto.
      -- custom70 h0 H2.
        --- custom18 h hj. apply S2.
          ---- eapply safe_pure_inv. eauto.
          ---- lia.
        --- edestruct safe_red as ( h1' & hj' & A & B & C & D ).
          ---- eauto.
          ---- eauto.
          ---- eauto.
          ---- eauto.
          ---- custom18 h1' hj'.
Qed.
Lemma triple_let : forall c f ( J : invariant ) ( P : precond ) ( Q R : postcond ), J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> ( forall v, J ⊢ ⦃ Q v ⦄ f v ⦃ R ⦄ ) -> J ⊢ ⦃ P ⦄ LET c f ⦃ R ⦄ .
Proof.
   intros c f J P Q R H H0. custom40 n h H1. custom46 safe_let Q H v n' h' H2 H3. custom7 H0.
Qed.
Corollary triple_seq : forall c1 c2 ( J : invariant ) ( P Q : precond ) ( R : postcond ), J ⊢ ⦃ P ⦄ c1 ⦃ fun _ => Q ⦄ -> J ⊢ ⦃ Q ⦄ c2 ⦃ R ⦄ -> J ⊢ ⦃ P ⦄ SEQ c1 c2 ⦃ R ⦄ .
Proof.
   intros c1 c2 J P Q R H H0. apply triple_let with ( fun _ => Q ).
    - auto.
    - auto.
Qed.
Lemma safe_ifthenelse : forall n b c1 c2 h Q J, ( b <> 0 -> safe n c1 h Q J ) -> ( b = 0 -> safe n c2 h Q J ) -> safe ( S n ) ( IFTHENELSE b c1 c2 ) h Q J .
Proof.
   intros n b c1 c2 h Q J H H0. custom15 hf hj h0 c' h' H1 H2 H3 H4 hf hj h0 H1 H2 H3 ST h. destruct ( Z.eqb_spec b 0 ) as [  e | n0 ].
    - auto.
    - auto.
Qed.
Lemma triple_ifthenelse : forall J b c1 c2 P Q, J ⊢ ⦃ ( b <> 0 ) //\\ P ⦄ c1 ⦃ Q ⦄ -> J ⊢ ⦃ ( b = 0 ) //\\ P ⦄ c2 ⦃ Q ⦄ -> J ⊢ ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ .
Proof.
   intros J b c1 c2 P Q H H0. custom40 n h H1. custom35 n. custom13 safe_ifthenelse H2.
    - custom56 H.
    - intros H2. custom56 H0.
Qed.
Lemma triple_repeat : forall J P c Q, J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> aimp ( Q 0 ) P -> J ⊢ ⦃ P ⦄ REPEAT c ⦃ fun v => ( v <> 0 ) //\\ Q v ⦄ .
Proof.
   intros J P c Q TR IMP. red. custom55 n.
    - custom75 h Ph.
    - intros h Ph. custom15 hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1 ST h. custom46 safe_let Q TR v n' h' H0 H2. custom35 n'. custom13 safe_ifthenelse H3.
      -- custom35 n'. custom58.
      -- intros H3. apply safe_mono with n.
        --- custom6 IHn IMP. congruence.
        --- lia.
Qed.
Lemma safe_par : forall ( J : invariant ) ( Q1 Q2 : assertion ) n c1 h1 c2 h2, safe n c1 h1 ( fun _ => Q1 ) J -> safe n c2 h2 ( fun _ => Q2 ) J -> hdisjoint h1 h2 -> safe n ( PAR c1 c2 ) ( hunion h1 h2 ) ( fun _ => Q1 ** Q2 ) J .
Proof.
   intros J Q1 Q2 n. custom71 n h2.
    - intros S1 S2 DISJ. constructor.
    - intros until h2. intros S1 S2 DISJ. custom26 hf hj h c' h' H H0 H1 H2 hf hj h H H0 H1 H2 l H.
      -- destruct H as [ H | H ].
        --- custom52 safe_immacc h1 h1 H. custom48 h1 l. custom42 hunion_comm h1 H3 hunion_assoc H3. custom42 hunion_comm h1 H3 hunion_assoc H3. custom42 hunion_comm h1 H3 hunion_assoc H3. rewrite hunion_assoc in H3.
        --- custom52 safe_immacc h1 h2 H. destruct ( h1 l ) as [ z'| ].
          ---- congruence.
          ---- congruence.
      -- custom72 ST.
        --- custom64 safe_immacc h1 h1 IM1. custom64 safe_immacc h1 h2 IM2. tauto.
        --- destruct H3 as [ IM1 IM2 ]. custom14 hj h2 hf S1 hunion_comm hunion_assoc.
        --- specialize ( DISJ l ). custom14 hj h1 hf S2 hunion_comm hunion_assoc.
      -- apply safe_pure_inv in S1. exists ( hunion h1 h2 ), hj. intuition auto. apply safe_pure. custom18 h1 h2.
      -- apply safe_pure_inv in S2. destruct ( safe_red _ _ _ _ _ _ _ _ _ H3 S1 ) as ( h1' & hj' & A & B & C & D ).
        --- auto.
        --- HDISJ.
        --- subst h'. exists ( hunion h1' h2 ), hj'. custom4 IHn.
          ---- custom20 hunion_assoc hunion_comm h2.
          ---- assumption.
          ---- custom49 safe_mono S n.
          ---- HDISJ.
      -- rewrite hunion_assoc in H3. custom42 hunion_comm h2 H3 hunion_assoc H3. destruct ( safe_red _ _ _ _ _ _ _ _ _ H3 S2 ) as ( h2' & hj' & A & B & C & D ).
        --- auto.
        --- HDISJ.
        --- subst h'. exists ( hunion h2' h1 ), hj'. custom66.
          ---- HDISJ.
          ---- custom20 hunion_assoc hunion_comm h1.
          ---- split.
            ----- assumption.
            ----- rewrite hunion_comm by HDISJ. apply IHn.
              ------ custom49 safe_mono S n.
              ------ auto.
              ------ HDISJ.
Qed.
Lemma triple_par : forall J P1 c1 Q1 P2 c2 Q2, J ⊢ ⦃ P1 ⦄ c1 ⦃ fun _ => Q1 ⦄ -> J ⊢ ⦃ P2 ⦄ c2 ⦃ fun _ => Q2 ⦄ -> J ⊢ ⦃ P1 ** P2 ⦄ PAR c1 c2 ⦃ fun _ => Q1 ** Q2 ⦄ .
Proof.
   intros until Q2. intros TR1 TR2 n h Ph. destruct Ph as ( h1 & h2 & Ph1 & Ph2 & D & U ). custom19 h safe_par.
Qed.
Lemma triple_get : forall J l v, J ⊢ ⦃ contains l v ⦄ GET l ⦃ fun v' => ( v' = v ) //\\ contains l v ⦄ .
Proof.
   intros J l v n h Ph. assert ( L : h l = Some v ) by ( rewrite Ph ; apply hupdate_same ). custom35 n. custom26 hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1 H2 l0 H.
    - congruence.
    - subst h0. intro ST. inv ST. custom37 H2 L H2.
    - assert ( v0 = v ).
      -- custom37 H3 L H3.
      -- subst v0. custom18 h hj. custom56 safe_pure.
Qed.
Lemma triple_set : forall J l v, J ⊢ ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄ .
Proof.
   intros J l v n h Ph. custom0 Ph Ph h l v0 Ph n hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1 l0 H ST H2 H3 L H3. exists ( hupdate l v hempty ), hj. custom9 Ph safe_pure heap_extensionality l0.
    - custom12 l0 H l.
    - custom12 l0 H0 l.
    - destruct ( Z.eq_dec l l0 ) as [  e | n0 ].
      -- auto.
      -- auto.
Qed.
Remark valid_N_init : forall sz l, ( valid_N l sz ) ( hinit l sz hempty ) .
Proof.
   intro sz. induction sz as [ | sz ].
    - custom57 l. custom11.
    - custom57 l. exists ( hupdate l 0 hempty ), ( hinit ( l + 1 ) sz hempty ). custom66.
      -- exists 0. custom11.
      -- apply IHsz.
      -- split.
        --- intros x. unfold hupdate, hempty at 1. custom29 l x. right. rewrite hinit_outside by lia. auto.
        --- custom13 heap_extensionality x. custom29 l x. auto.
Qed.
Lemma triple_alloc : forall J sz, J ⊢ ⦃ emp ⦄ ALLOC sz ⦃ fun l => ( l <> 0 ) //\\ valid_N l sz ⦄ .
Proof.
   intros J sz n h Ph. red in Ph. subst h. custom25 n hf hj h c' h' H H0 H1 H2 hf hj h H H0 H1 ST.
    - inv ST.
    - rewrite hunion_empty in H0. custom70 h H2. exists ( hinit l sz hempty ), hj. custom74 safe_pure.
      -- assert ( D : hdisjoint ( hinit l sz hempty ) ( hunion hj hf ) ).
        --- red. intros l0. assert ( EITHER : l <= l0 < l + Z.of_nat sz \/ l0 < l \/ l + Z.of_nat sz <= l0 ) by lia. destruct EITHER as [  H0 | H0 ].
          ---- right. auto.
          ---- left. custom7 hinit_outside.
        --- HDISJ.
      -- custom13 heap_extensionality l0. cbn. assert ( EITHER : l <= l0 < l + Z.of_nat sz \/ l0 < l \/ l + Z.of_nat sz <= l0 ) by lia. destruct EITHER as [  H0 | H0 ].
        --- custom60 hinit_inside.
        --- custom60 hinit_outside.
      -- split.
        --- auto.
        --- apply valid_N_init.
Qed.
Lemma triple_free : forall J l, J ⊢ ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄ .
Proof.
   intros J l n h Ph. custom0 Ph Ph h l v0 Ph n hf hj h0 c' h' H H0 H1 H2 hf hj h0 H H0 H1 l0 H ST H2 H3 L H3. exists hempty, hj. custom74 safe_pure.
    - HDISJ.
    - assert ( D : hdisjoint ( hupdate l v0 hempty ) ( hunion hj hf ) ) by HDISJ. custom54 Ph heap_extensionality l0. custom29 l l0. subst l0. destruct ( D l ) as [  H0 | H0 ].
      -- rewrite hupdate_same in H0. congruence.
      -- auto.
    - reflexivity.
Qed.
Lemma triple_consequence_pre : forall P' J P c Q, J ⊢ ⦃ P' ⦄ c ⦃ Q ⦄ -> aimp P P' -> J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P' J P c Q H H0. intros n h Ph. custom7 H.
Qed.
Lemma safe_consequence : forall ( Q Q' : postcond ) ( J : invariant ), ( forall v, aimp ( Q' v ) ( Q v ) ) -> forall n c h, safe n c h Q' J -> safe n c h Q J .
Proof.
   intros Q Q' J H n. custom17 n c h H0 c h H0.
    - custom7 H.
    - custom24 hf hj h0 c' h' H0 H1 H2 H3. edestruct STEP as ( h1' & hj' & A & B & C & D ).
      -- eauto.
      -- eauto.
      -- eauto.
      -- eauto.
      -- custom18 h1' hj'.
Qed.
Lemma triple_consequence_post : forall Q' J P c Q, J ⊢ ⦃ P ⦄ c ⦃ Q' ⦄ -> ( forall v, aimp ( Q' v ) ( Q v ) ) -> J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros Q' J P c Q H H0. intros n h Ph. apply safe_consequence with Q'.
    - auto.
    - auto.
Qed.
Lemma triple_exists_pre : forall { X : Type } J ( P : X -> assertion ) c Q, ( forall v, J ⊢ ⦃ P v ⦄ c ⦃ Q ⦄ ) -> J ⊢ ⦃ aexists P ⦄ c ⦃ Q ⦄ .
Proof.
   custom78 X J P c Q H n h Ph. destruct Ph as ( v & Ph ). apply ( H v ). auto.
Qed.
Lemma triple_simple_conj_pre : forall J ( P1 : Prop ) P2 c Q, ( P1 -> J ⊢ ⦃ P2 ⦄ c ⦃ Q ⦄ ) -> J ⊢ ⦃ P1 //\\ P2 ⦄ c ⦃ Q ⦄ .
Proof.
   custom78 J P1 P2 c Q H n h Ph. destruct Ph as [  H1 H0 ]. custom59 H.
Qed.
Lemma triple_or : forall J P c Q P' Q', J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P' ⦄ c ⦃ Q' ⦄ -> J ⊢ ⦃ aor P P' ⦄ c ⦃ fun v => aor ( Q v ) ( Q' v ) ⦄ .
Proof.
   intros until Q'. intros TR1 TR2 n h [ P'h | TR1 ].
    - custom30 safe_consequence Q v1 h1 TR1.
    - apply safe_consequence with Q'.
      -- intros v1 h1. custom11.
      -- custom7 TR2.
Qed.
Lemma safe_and : forall J Q Q', precise J -> forall n c h, safe n c h Q J -> safe n c h Q' J -> safe n c h ( fun v => aand ( Q v ) ( Q' v ) ) J .
Proof.
   intros J Q Q' H n. induction n.
    - intros c h S S'. constructor.
    - intros c h S S'. inv S.
      -- custom76 S'. custom58.
      -- custom77 S'. custom24 hf hj h0 c' h' H0 H1 H2 H3. edestruct STEP as ( h1' & hj' & D' & E' & J' & SAFE' ).
        --- eauto.
        --- eauto.
        --- eauto.
        --- eauto.
        --- edestruct STEP0 as ( h1'' & hj'' & D'' & E'' & J'' & SAFE'' ).
          ---- eauto.
          ---- eauto.
          ---- eauto.
          ---- eauto.
          ---- custom69 hj' hj''.
            ----- apply H with ( hunion h1' hf ) ( hunion h1'' hf ).
              ------ HDISJ.
              ------ HDISJ.
              ------ rewrite ! ( hunion_comm hf ) by HDISJ. rewrite <- ! hunion_assoc. rewrite ( hunion_comm h1' ), ( hunion_comm h1'' ) by HDISJ. congruence.
              ------ auto.
              ------ auto.
            ----- custom69 h1' h1''.
              ------ apply hunion_invert_l with ( hunion hj' hf ).
                ------- congruence.
                ------- HDISJ.
                ------- HDISJ.
              ------ custom38 h1' hj'.
Qed.
Lemma triple_and : forall J P c Q P' Q', precise J -> J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P' ⦄ c ⦃ Q' ⦄ -> J ⊢ ⦃ aand P P' ⦄ c ⦃ fun v => aand ( Q v ) ( Q' v ) ⦄ .
Proof.
   intros until Q'. intros PR TR1 TR2 n h ( Ph & P'h ). custom59 safe_and. auto.
Qed.
Lemma triple_swap : forall lck R, sem_invariant lck R ⊢ ⦃ emp ⦄ SWAP lck 0 ⦃ fun v => if Z.eqb v 0 then emp else R ⦄ .
Proof.
   intros lck R. custom68 triple_atomic sepconj_emp. unfold sem_invariant at 1. custom13 triple_exists_pre v. eapply triple_let with ( Q := fun v' => ( ( v' = v ) //\\ contains lck v ) ** ( if v =? 0 then emp else R ) ).
    - custom6 triple_frame triple_get.
    - custom33 v' lift_pureconj triple_simple_conj_pre EQ. apply triple_seq with ( Q := contains lck 0 ** ( if v =? 0 then emp else R ) ).
      -- custom23 triple_frame triple_consequence_pre valid lck triple_set h H v.
      -- custom67 triple_pure sem_invariant. red. intros h H. rewrite sepconj_comm, lift_aexists. exists 0. rewrite Z.eqb_refl. rewrite <- ( sepconj_comm emp ), sepconj_emp. assumption.
Qed.
Lemma triple_acquire : forall lck R, sem_invariant lck R ⊢ ⦃ emp ⦄ ACQUIRE lck ⦃ fun _ => R ⦄ .
Proof.
   intros lck R. apply triple_consequence_post with ( Q' := fun v => ( v <> 0 ) //\\ ( if Z.eqb v 0 then emp else R ) ).
    - custom6 triple_repeat triple_swap. custom41 Z.eqb_refl.
    - custom63 v h H1 H2 Z.eqb_neq H1.
Qed.
Lemma triple_release : forall lck R, precise R -> sem_invariant lck R ⊢ ⦃ R ⦄ RELEASE lck ⦃ fun _ => emp ⦄ .
Proof.
   intros lck R H. custom68 triple_atomic sepconj_comm. unfold sem_invariant at 1. custom54 lift_aexists triple_exists_pre v. rewrite sepconj_assoc. apply triple_consequence_post with ( Q' := fun _ => contains lck 1 ** ( if v =? 0 then emp else R ) ** R ).
    - custom23 triple_frame triple_consequence_pre valid lck triple_set h H0 v.
    - intros _. intros h P. assert ( ( contains lck 1 ** R ) h ).
      -- eapply sepconj_imp_r with ( P := ( if v =? 0 then emp else R ) ** R ).
        --- destruct ( v =? 0 ) as [  P | P ].
          ---- custom41 sepconj_emp.
          ---- custom7 sepconj_self.
        --- eauto.
      -- rewrite sepconj_emp. exists 1. simpl. auto.
Qed.
Lemma triple_critregion : forall lck R c P Q, precise R -> emp ⊢ ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ -> sem_invariant lck R ⊢ ⦃ P ⦄ CRITREGION lck c ⦃ Q ⦄ .
Proof.
   intros lck R c P Q H H0. custom44 triple_seq Q R P sepconj_emp triple_frame triple_acquire. eapply triple_let.
    - rewrite sepconj_comm. rewrite <- sepconj_emp at 1. custom6 triple_frame_invariant H0.
    - intros v. simpl. apply triple_seq with ( Q := emp ** Q v ).
      -- rewrite sepconj_comm. custom6 triple_frame triple_release. auto.
      -- rewrite sepconj_emp. apply triple_pure. custom11.
Qed.
Lemma triple_ccr : forall lck R b c B P Q, precise R -> emp ⊢ ⦃ P ** R ⦄ b ⦃ fun v => if v =? 0 then P ** R else B ⦄ -> emp ⊢ ⦃ B ⦄ c ⦃ fun _ => Q ** R ⦄ -> sem_invariant lck R ⊢ ⦃ P ⦄ CCR lck b c ⦃ fun _ => Q ⦄ .
Proof.
   intros lck R b c B P Q H H0 H1. set ( Qloop := fun v => if v =? 0 then P else Q ). apply triple_consequence_post with ( fun v => ( v <> 0 ) //\\ Qloop v ).
    - apply triple_repeat.
      -- custom44 triple_seq Q R P sepconj_emp triple_frame triple_acquire. rewrite sepconj_comm at 1. custom31 triple_let sepconj_emp triple_frame_invariant H0. intros v. apply triple_ifthenelse.
        --- eapply triple_seq.
          ---- custom31 triple_consequence_pre sepconj_emp triple_frame_invariant H1. intros h ( X & Y ). custom21 Z.eqb_neq X X Y.
          ---- apply triple_seq with ( Q := emp ** Q ).
            ----- custom39 sepconj_comm triple_frame triple_release.
            ----- custom22 triple_pure sepconj_emp Qloop.
        --- apply triple_consequence_pre with ( P ** R ).
          ---- eapply triple_seq with ( Q := emp ** P ).
            ----- custom39 sepconj_comm triple_frame triple_release.
            ----- custom22 triple_pure sepconj_emp Qloop.
          ---- intros h ( X & Y ). subst v. auto.
      -- unfold Qloop. intros v U. simpl in U. auto.
    - intros v h ( U & V ). red in V. custom21 Z.eqb_neq U U V.
Qed.
Remark precise_buffer_invariant : forall ( R : Z -> assertion ) buff, ( forall v, precise ( R v ) ) -> precise ( aexists ( fun v => contains buff v ** R v ) ) .
Proof.
   intros R buff H. custom6 aexists_precise sepconj_param_precise.
    - apply contains_param_precise.
    - auto.
Qed.
Lemma triple_consume : forall R buff free busy, buffer_invariant R buff free busy ⊢ ⦃ emp ⦄ CONSUME buff free busy ⦃ fun v => R v ⦄ .
Proof.
   intros R buff free busy. eapply triple_seq.
    - custom53 buffer_invariant sepconj_comm. custom6 triple_frame_invariant triple_acquire.
    - custom73 triple_exists_pre v triple_let v' lift_pureconj triple_simple_conj_pre EQ triple_frame triple_get. apply triple_seq with ( emp ** R v ).
      -- unfold buffer_invariant. custom6 triple_frame_invariant triple_frame. custom32 triple_consequence_pre triple_release valid_precise h H v.
      -- apply triple_pure. custom41 sepconj_emp.
Qed.
Lemma triple_produce : forall ( R : Z -> assertion ) buff free busy data, ( forall v, precise ( R v ) ) -> buffer_invariant R buff free busy ⊢ ⦃ R data ⦄ PRODUCE buff free busy data ⦃ fun _ => emp ⦄ .
Proof.
   intros R buff free busy data H. apply triple_seq with ( valid buff ** R data ).
    - unfold buffer_invariant. apply triple_frame_invariant. rewrite <- ( sepconj_emp ( R data ) ) at 1. custom6 triple_frame triple_acquire.
    - apply triple_seq with ( contains buff data ** R data ).
      -- custom6 triple_frame triple_set.
      -- custom53 buffer_invariant sepconj_comm. apply triple_frame_invariant. custom32 triple_consequence_pre triple_release precise_buffer_invariant h H0 data. assumption.
Qed.
Lemma triple_pop : forall R buff, buffer_invariant R buff ⊢ ⦃ emp ⦄ POP buff ⦃ fun p => aexists ( fun x => contains p x ** valid ( p + 1 ) ** R x ) ⦄ .
Proof.
   intros R buff. set ( Qloop := fun p => if p =? 0 then emp else aexists ( fun x => contains p x ** valid ( p + 1 ) ** R x ) ). apply triple_consequence_post with ( fun p => ( p <> 0 ) //\\ Qloop p ).
    - custom6 triple_repeat triple_atomic.
      -- custom54 sepconj_emp triple_exists_pre l. custom13 triple_exists_pre p. eapply triple_let.
        --- custom6 triple_frame triple_get.
        --- cbn. custom33 p' lift_pureconj triple_simple_conj_pre E. custom6 triple_ifthenelse triple_simple_conj_pre.
          ---- intros NOTZERO. rewrite sepconj_comm. destruct l as [apply Z.eqb_neq in NOTZERO | x l ].
            ----- custom28 lift_pureconj triple_simple_conj_pre H. try lia.
            ----- custom28 lift_pureconj triple_simple_conj_pre H. rewrite lift_aexists. custom5 triple_exists_pre t triple_let t' lift_pureconj triple_simple_conj_pre E.
              ------ rewrite ! sepconj_assoc, sepconj_pick2. custom6 triple_frame triple_get.
              ------ rewrite <- ! sepconj_assoc, sepconj_comm, ! sepconj_assoc. custom65 triple_seq triple_pure.
                ------- apply triple_frame with ( Q := fun _ => contains buff t ). custom47 triple_consequence_pre triple_set h A p.
                ------- custom53 Qloop NOTZERO. rewrite ( sepconj_pick2 ( contains p x ) ). rewrite <- ( sepconj_pick3 ( contains buff t ) ). rewrite <- ( sepconj_pick2 ( contains buff t ) ). intros h A. rewrite lift_aexists. exists x. rewrite ! sepconj_assoc. eapply sepconj_imp_r with ( P := contains ( p + 1 ) t ** R x ** contains buff t ** list_invariant R l t ).
                  -------- intros h' B. apply sepconj_imp_l with ( P := contains ( p + 1 ) t ).
                    --------- custom10 h'' C t.
                    --------- revert h' B. custom6 sepconj_imp_r sepconj_imp_r. intros h''' D. red. exists l. exists t. auto.
                  -------- eauto.
          ---- custom13 triple_simple_conj_pre ZERO. custom67 triple_pure Qloop. cbn. rewrite sepconj_emp. intros h A. custom38 l p.
      -- unfold Qloop. cbn. custom11.
    - unfold Qloop. custom63 v h A B Z.eqb_neq A.
Qed.
Lemma triple_consume2 : forall R buff, buffer_invariant R buff ⊢ ⦃ emp ⦄ CONSUME buff ⦃ fun data => R data ⦄ .
Proof.
   intros R buff. eapply triple_let.
    - apply triple_pop.
    - custom57 b. custom73 triple_exists_pre p triple_let p' lift_pureconj triple_simple_conj_pre E triple_frame triple_get. eapply triple_seq.
      -- apply triple_frame with ( Q := fun _ => emp ). custom47 triple_consequence_pre triple_free h A p.
      -- rewrite sepconj_emp. custom65 triple_seq triple_pure.
        --- apply triple_frame with ( Q := fun _ => emp ). apply triple_free.
        --- custom41 sepconj_emp.
Qed.

Ltac custom0 H0 H33 H1 H4 H7 H6 H2 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H26 H27 H28 H25 H30 H8 H31 :=  destruct H0 as ( v0 & H33 ); [assert ( L : H1 H4 = Some H7 ) by ( rewrite H6 ; apply hupdate_same ); [destruct H2; [constructor | constructor; [auto | cbn; [intros H26 H27; [congruence | .. ] | .. ] | intros H18 H19 H20 H21 H22 H23; [intro H28; [inv H28; [congruence] | .. ] | .. ] | intros H9 H10 H11 H12 H13 H14 H15 H16 H17; [rewrite H6 in H14; [subst H11; [inv H25; [cbn in H30; [rewrite H8 in H31] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom1 H0 H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H21 :=  intros H0 H1 H2 H3; [induction H3; [intros H5 H6 H7 H8 H9 H10; [constructor | .. ] | intros H11 H12 H13 H14 H15 H16; [inv H14; [constructor; [exists H12, H13; [auto | .. ] | .. ] | constructor; [auto | intros H32 H33; [apply H21 in H33; [cbn; [destruct ( H12 H32 ) as [ z| ]; [congruence | congruence | .. ] | .. ] | .. ] | .. ] | intros H34 H35 H36 H37 H38 H39 | intros H23 H24 H25 H26 H27 H28 H29 H30 H31 | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom2 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 :=  constructor; [auto |  | intros H11 H12 H13 H14 H15 H16 | intros H2 H3 H4 H5 H6 H7 H8 H9 H10 | .. ].
Ltac custom3 H0 H11 H12 H13 H14 H15 H16 H17 H18 H19 H3 H25 H24 :=  inv H0; [constructor; [auto | .. ] | constructor; [auto | auto | auto | intros H11 H12 H13 H14 H15 H16 H17 H18 H19; [edestruct H3 as ( h1' & hj' & A & B & C & D ); [eauto | eauto | eauto | eauto | exists H25, H24 | .. ] | .. ] | .. ] | .. ].
Ltac custom4 H6 :=  split; [HDISJ | split; [ | split; [ | apply H6; [auto | .. ] | .. ] | .. ] | .. ].
Ltac custom5 H0 H1 H2 H3 H4 H5 H6 :=  apply H0; [intros H1; [eapply H2; [ | intros H3; [cbn; [rewrite H4; [apply H5; [intros H6; [subst H3 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom6 H0 H1 :=  apply H0; [apply H1 | .. ].
Ltac custom7 H0 :=  apply H0; [auto | .. ].
Ltac custom8 H10 H11 H9 H8 :=  edestruct safe_redN as ( h1' & hj' & A & B & C & D ); [eexact H10 | apply H11; [exists H9, H8; [intuition auto; [HDISJ | .. ] | .. ] | .. ] | reflexivity | HDISJ | .. ].
Ltac custom9 H6 H21 H22 H23 :=  intuition auto; [HDISJ | rewrite H6; [apply H22; [intros H23; [cbn | .. ] | .. ] | .. ] | apply H21; [reflexivity | .. ] | .. ].
Ltac custom10 H0 H1 H2 :=  intros H0 H1; [exists H2; [auto | .. ] | .. ].
Ltac custom11  :=  red; [auto | .. ].
Ltac custom12 H0 H1 H2 :=  red; [intros H0; [generalize ( H1 H0 ); [cbn; [destruct ( Z.eq_dec H2 H0 ); [intuition congruence | intuition congruence | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom13 H0 H1 :=  apply H0; [intros H1 | .. ].
Ltac custom14 H0 H1 H2 H3 H9 H14 :=  elim ( safe_not_erroneous _ _ _ _ _ H0 ( hunion H1 H2 ) H3 ); [HDISJ | auto | rewrite <- ( H9 H0 ) by HDISJ; [rewrite H14; [rewrite ( H9 H0 ) by HDISJ; [assumption | .. ] | .. ] | .. ] | .. ].
Ltac custom15 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H19 H15 :=  custom2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14; [auto | intro H19; [inv H19 | .. ] | inv H8; [exists H15, H1; [intuition auto | .. ] | .. ] | .. ].
Ltac custom16  :=  split; [auto | auto | .. ].
Ltac custom17 H0 H2 H3 H4 H5 H6 H7 :=  induction H0; [intros H2 H3 H4; [constructor | .. ] | intros H5 H6 H7; [inv H7; [constructor | .. ] | .. ] | .. ].
Ltac custom18 H0 H1 :=  exists H0, H1; [intuition auto | .. ].
Ltac custom19 H0 H2 :=  subst H0; [custom7 H2; [auto | auto | .. ] | .. ].
Ltac custom20 H0 H1 H2 :=  rewrite H0; [f_equal; [rewrite <- ( H1 H2 ) by HDISJ; [rewrite H0; [auto | .. ] | .. ] | .. ] | .. ].
Ltac custom21 H0 H1 H2 H3 :=  apply H0 in H1; [rewrite H2 in H3; [auto] | .. ].
Ltac custom22 H0 H1 H2 :=  apply H0; [rewrite H1; [unfold H2; [cbn; [custom11  | .. ] | .. ] | .. ] | .. ].
Ltac custom23 H0 H1 H2 H3 H4 H6 H7 H5 :=  apply H0; [apply H1 with ( H2 H3 ); [apply H4 | red; [custom10 H6 H7 H5 | .. ] | .. ] | .. ].
Ltac custom24 H6 H7 H8 H9 H10 H11 H12 H13 H14 :=  constructor; [auto | auto | auto | intros H6 H7 H8 H9 H10 H11 H12 H13 H14 | .. ].
Ltac custom25 H0 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 :=  destruct H0; [constructor | custom2 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21; [auto | intro H22 | .. ] | .. ].
Ltac custom26 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H24 H25 :=  custom2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14; [cbn; [intros H24 H25 | .. ] | subst H2 | inv H15; [ | .. ] | .. ].
Ltac custom27 H0 H1 H2 H3 :=  exists ( hunion H0 H1 ), H2; [custom4 H3; [ |  | HDISJ | auto | .. ] | .. ].
Ltac custom28 H0 H1 H2 :=  cbn; [rewrite H0; [apply H1; [intro H2 | .. ] | .. ] | .. ].
Ltac custom29 H0 H1 :=  cbn; [destruct ( Z.eq_dec H0 H1 ); [ | auto | .. ] | .. ].
Ltac custom30 H0 H1 H2 H3 H4 :=  apply H0 with H1; [intros H2 H3; [custom11  | .. ] | custom7 H4 | .. ].
Ltac custom31 H0 H1 H2 H3 :=  eapply H0; [rewrite <- H1 at 1; [apply H2; [eexact H3 | .. ] | .. ] | .. ].
Ltac custom32 H0 H1 H2 H4 H5 H3 :=  eapply H0; [custom6 H1 H2 | red; [custom10 H4 H5 H3 | .. ] | .. ].
Ltac custom33 H0 H1 H2 H3 :=  intros H0; [rewrite H1; [custom13 H2 H3; [subst H0 | .. ] | .. ] | .. ].
Ltac custom34 H0 H5 H2 H6 H14 H12 :=  inv H0; [apply H5 in H2; [destruct H6 as ( N & STEPS ); [rewrite <- H14 in H12] | .. ] | .. ].
Ltac custom35 H0 :=  destruct H0; [constructor | .. ].
Ltac custom36 H0 H1 :=  custom18 H0 H1; [HDISJ | .. ].
Ltac custom37 H0 H2 H1 :=  cbn in H0; [rewrite H2 in H1; [congruence] | .. ].
Ltac custom38 H0 H1 :=  exists H0, H1; [auto | .. ].
Ltac custom39 H0 H1 H2 :=  rewrite H0 at 1; [custom6 H1 H2; [auto | .. ] | .. ].
Ltac custom40 H0 H1 H2 :=  red; [intros H0 H1 H2 | .. ].
Ltac custom41 H0 :=  rewrite H0; [custom11  | .. ].
Ltac custom42 H0 H1 H2 H15 H14 :=  rewrite <- ( H0 H1 ) in H2 by HDISJ; [rewrite H15 in H14].
Ltac custom43 H0 :=  f_equal; [rewrite H0; [auto | .. ] | .. ].
Ltac custom44 H0 H1 H2 H3 H4 H5 H6 :=  apply H0 with ( H1 := H2 ** H3 ); [rewrite <- ( H4 H3 ) at 1; [custom6 H5 H6 | .. ] | .. ].
Ltac custom45 H0 :=  eapply H0; [eauto | eauto | .. ].
Ltac custom46 H0 H1 H2 H3 H4 H5 H6 H7 :=  apply H0 with H1; [custom7 H2 | intros H3 H4 H5 H6 H7 | .. ].
Ltac custom47 H0 H1 H3 H4 H2 :=  eapply H0; [apply H1 | custom10 H3 H4 H2 | .. ].
Ltac custom48 H0 H1 :=  destruct ( H0 H1 ) as [ z| ]; [congruence | congruence | .. ].
Ltac custom49 H0 H1 H2 :=  apply H0 with ( H1 H2 ); [auto | auto | .. ].
Ltac custom50 H0 H1 H2 H3 H4 :=  apply ( H0 ( H1 H2 H3 ) H4 ); [HDISJ |  | auto | .. ].
Ltac custom51 H0 H2 :=  subst H0; [rewrite ! H2; [auto | .. ] | .. ].
Ltac custom52 H0 H1 H6 H2 :=  eapply H0 with ( H1 := H6 ) in H2; [ | eauto | .. ].
Ltac custom53 H0 H1 :=  unfold H0; [rewrite H1 | .. ].
Ltac custom54 H0 H1 H2 :=  rewrite H0; [custom13 H1 H2 | .. ].
Ltac custom55 H0 :=  intro H0; [induction H0 | .. ].
Ltac custom56 H0 :=  apply H0; [custom16  | .. ].
Ltac custom57 H0 :=  intros H0; [cbn | .. ].
Ltac custom58  :=  constructor; [custom16  | .. ].
Ltac custom59 H0 :=  custom7 H0; [auto | .. ].
Ltac custom60 H0 :=  rewrite ! H0 by auto; [auto | .. ].
Ltac custom61  :=  eelim safe_not_erroneous; [ |  | eauto | .. ].
Ltac custom62 H0 H4 H11 :=  rewrite H0 by HDISJ; [custom36 H4 H11 | .. ].
Ltac custom63 H0 H1 H2 H3 H4 H5 :=  intros H0 H1 [ H2 H3 ]; [custom21 H4 H2 H5 H3 | .. ].
Ltac custom64 H0 H1 H6 H2 :=  eapply H0 with ( H1 := H6 ) in H2; [ | eauto | .. ].
Ltac custom65 H0 H1 :=  eapply H0; [ | apply H1 | .. ].
Ltac custom66  :=  split; [ | split | .. ].
Ltac custom67 H0 H1 :=  apply H0; [unfold H1 | .. ].
Ltac custom68 H0 H1 :=  apply H0; [rewrite H1 | .. ].
Ltac custom69 H0 H1 :=  assert ( H0 = H1 ); [ | subst H1 | .. ].
Ltac custom70 H0 H2 :=  subst H0; [inv H2].
Ltac custom71 H0 H2 :=  induction H0; [intros until H2 | .. ].
Ltac custom72 H0 :=  intros H0; [inv H0 | .. ].
Ltac custom73 H0 H4 H1 H5 H2 H3 H6 H7 H8 :=  custom5 H0 H4 H1 H5 H2 H3 H6; [custom6 H7 H8 | .. ].
Ltac custom74 H13 :=  intuition auto; [ |  | apply H13 | .. ].
Ltac custom75 H0 H1 :=  intros H0 H1; [constructor | .. ].
Ltac custom76 H0 :=  inv H0; [ | contradiction | .. ].
Ltac custom77 H0 :=  inv H0; [contradiction | .. ].
Ltac custom78 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1 H2 H3 H4 H5; [intros H6 H7 H8 | .. ].
Ltac custom79 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1 H2 H3 H4 H5; [custom40 H6 H7 H8 | .. ].
