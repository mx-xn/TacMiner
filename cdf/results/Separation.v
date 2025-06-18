Lemma heap_extensionality : forall ( h1 h2 : heap ), ( forall l, h1 l = h2 l ) -> h1 = h2 .
Proof.
   intros h1 h2 H. destruct h1 as [ c1 fin1 ], h2 as [ c2 fin2 ]. assert ( c1 = c2 ) by ( apply functional_extensionality ; auto ). subst c2. f_equal. apply proof_irrelevance.
Qed.
Lemma hempty_dup A : exists i : Z, forall j : Z, i <= j -> @None A = None .
Proof.
   exists 0. auto.
Qed.
Lemma hupdate_dup ( l : addr ) ( v : Z ) ( h : heap ) : exists i : Z, forall j : Z, i <= j -> ( if Z.eq_dec l j then Some v else h j ) = None .
Proof.
   destruct ( isfinite h ) as ( i & fin ). exists ( Z.max i ( l + 1 ) ). custom29 j H l.
    - lia.
    - apply fin. lia.
Qed.
Lemma hupdate_same : forall l v h, ( hupdate l v h ) l = Some v .
Proof.
   intros l v h. custom23 l l.
    - congruence.
    - congruence.
Qed.
Lemma hupdate_other : forall l v h l', l <> l' -> ( hupdate l v h ) l' = h l' .
Proof.
   intros l v h l' H. custom23 l l'.
    - congruence.
    - congruence.
Qed.
Lemma hfree_dup ( l : addr ) ( h : heap ) : exists i : Z, forall j : Z, i <= j -> ( if Z.eq_dec l j then None else h j ) = None .
Proof.
   destruct ( isfinite h ) as ( i & fin ). exists i. custom29 j H l.
    - auto.
    - auto.
Qed.
Lemma hinit_inside : forall h sz l l', l <= l' < l + Z.of_nat sz -> hinit l sz h l' = Some 0 .
Proof.
   custom1 h sz IHsz l l' H l l' IHsz.
    - lia.
    - auto.
    - lia.
Qed.
Lemma hinit_outside : forall h sz l l', l' < l \/ l + Z.of_nat sz <= l' -> hinit l sz h l' = h l' .
Proof.
   custom1 h sz IHsz l l' H l l' IHsz.
    - auto.
    - lia.
    - lia.
Qed.

Lemma hdisjoint_sym : forall h1 h2, hdisjoint h1 h2 <-> hdisjoint h2 h1 .
Proof.
   unfold hdisjoint. intros h1 h2. split.
    - custom16 H l.
    - custom16 H l.
Qed.
Lemma hunion_dup ( h1 h2 : heap ) : exists i : Z, forall j : Z, i <= j -> ( if h1 j then h1 j else h2 j ) = None .
Proof.
   destruct ( isfinite h1 ) as ( i1 & fin1 ), ( isfinite h2 ) as ( i2 & fin2 ). exists ( Z.max i1 i2 ). intros j H. rewrite fin1, fin2 by lia. auto.
Qed.
Lemma hunion_comm : forall h1 h2, hdisjoint h1 h2 -> hunion h2 h1 = hunion h1 h2 .
Proof.
   custom20 h1 h2 H heap_extensionality l. cbn. specialize ( H l ). destruct ( h1 l ) as [ z| ], ( h2 l ) as [ z'| ].
    - intuition congruence.
    - intuition congruence.
    - intuition congruence.
    - intuition congruence.
Qed.
Lemma hunion_assoc : forall h1 h2 h3, hunion ( hunion h1 h2 ) h3 = hunion h1 ( hunion h2 h3 ) .
Proof.
   custom20 h1 h2 h3 heap_extensionality l. custom8 h1 l.
Qed.
Lemma hunion_empty : forall h, hunion hempty h = h .
Proof.
   intros h. custom0 heap_extensionality l. cbn. auto.
Qed.
Lemma hdisjoint_union_l : forall h1 h2 h3, hdisjoint ( hunion h1 h2 ) h3 <-> hdisjoint h1 h3 /\ hdisjoint h2 h3 .
Proof.
   unfold hdisjoint, hunion. cbn. custom33 h1 h2 h3 D.
    - split.
      -- custom11 l D h1.
        --- auto.
        --- auto.
      -- custom11 l D h1.
        --- discriminate.
        --- auto.
    - intros [ D1 D2 ] l. destruct ( D2 l ) as [ z| ].
      -- destruct ( h1 l ) as [ z'| ] eqn : H1.
        --- destruct ( D1 l ) as [ z''| ].
          ---- congruence.
          ---- auto.
        --- auto.
      -- auto.
Qed.
Lemma hdisjoint_union_r : forall h1 h2 h3, hdisjoint h1 ( hunion h2 h3 ) <-> hdisjoint h1 h2 /\ hdisjoint h1 h3 .
Proof.
   intros h1 h2 h3. rewrite hdisjoint_sym. rewrite hdisjoint_union_l. rewrite ( hdisjoint_sym h2 ), ( hdisjoint_sym h3 ). tauto.
Qed.
Lemma hunion_invert_r : forall h1 h2 h, hunion h h1 = hunion h h2 -> hdisjoint h h1 -> hdisjoint h h2 -> h1 = h2 .
Proof.
   intros h1 h2 h H H0 H1. custom0 heap_extensionality l. assert ( hunion h h1 l = hunion h h2 l ) by congruence. cbn in H2. specialize ( H0 l ). specialize ( H1 l ). destruct ( h l ) as [ z| ].
    - intuition congruence.
    - intuition congruence.
Qed.
Lemma hunion_invert_l : forall h1 h2 h, hunion h1 h = hunion h2 h -> hdisjoint h1 h -> hdisjoint h2 h -> h1 = h2 .
Proof.
   intros h1 h2 h H H0 H1. apply hunion_invert_r with h.
    - rewrite <- ! ( hunion_comm h ) by HDISJ. auto.
    - HDISJ.
    - HDISJ.
Qed.
Lemma assertion_extensionality : forall ( P Q : assertion ), ( forall h, P h <-> Q h ) -> P = Q .
Proof.
   custom20 P Q H functional_extensionality h. custom4 propositional_extensionality.
Qed.
Lemma sepconj_comm : forall P Q, P ** Q = Q ** P .
Proof.
   assert ( forall P Q h, ( P ** Q ) h -> ( Q ** P ) h ).
    - custom28 P Q h h1 h2 P1 Q2 EQ DISJ. custom7 h2 h1.
      -- custom4 hdisjoint_sym.
      -- symmetry. custom4 hunion_comm.
    - custom17 P Q assertion_extensionality h. custom15.
Qed.
Lemma sepconj_assoc : forall P Q R, ( P ** Q ) ** R = P ** ( Q ** R ) .
Proof.
   custom6 P Q R assertion_extensionality h.
    - intros ( hx & h3 & ( h1 & h2 & P1 & Q2 & EQ & DISJ ) & R3 & EQ' & DISJ' ). subst hx h. rewrite hunion_assoc. exists h1, ( hunion h2 h3 ). custom3 hdisjoint_union_l EQ' h2 h3 hdisjoint_union_r.
    - intros ( h1 & hx & P1 & ( h2 & h3 & Q2 & R3 & EQ & DISJ ) & EQ' & DISJ' ). subst hx h. rewrite hdisjoint_union_r in EQ'. rewrite <- hunion_assoc. exists ( hunion h1 h2 ), h3. intuition auto.
      -- custom7 h1 h2.
      -- rewrite hdisjoint_union_l. tauto.
Qed.
Lemma sepconj_emp : forall P, emp ** P = P .
Proof.
   intros P. custom0 assertion_extensionality h. split.
    - intros ( h1 & h2 & EMP1 & P2 & EQ & DISJ ). red in EMP1. custom32 h h1 hunion_empty.
    - intros H. exists hempty, h. intuition auto.
      -- custom21.
      -- custom21.
      -- custom5 hunion_empty.
Qed.
Lemma sepconj_imp_l : forall P Q R, ( P -->> Q ) -> ( P ** R -->> Q ** R ) .
Proof.
   intros P Q R IMP h ( h1 & h2 & P1 & Q2 & D & U ). custom7 h1 h2.
Qed.
Lemma sepconj_imp_r : forall P Q R, ( P -->> Q ) -> ( R ** P -->> R ** Q ) .
Proof.
   intros P Q R H. rewrite ! ( sepconj_comm R ). custom4 sepconj_imp_l.
Qed.
Lemma pure_sep : forall P Q, pure ( P /\ Q ) = pure P ** pure Q .
Proof.
   custom17 P Q assertion_extensionality h. unfold pure, sepconj. split.
    - intros ( ( A & B ) & C ). subst h. exists hempty, hempty. custom10 l hunion_empty.
    - intros ( h1 & h2 & ( PP & E1 ) & ( QQ & E2 ) & C & D ). subst h h1 h2. custom5 hunion_empty.
Qed.
Lemma pureconj_sepconj : forall P Q, pure P ** Q = P //\\ Q .
Proof.
   custom17 P Q assertion_extensionality h. unfold pure, sepconj, pureconj. split.
    - intros ( h1 & h2 & ( A & B ) & C & D & E ). split.
      -- auto.
      -- custom32 h h1 hunion_empty.
    - intros ( A & B ). exists hempty, h. custom10 l hunion_empty.
Qed.
Lemma lift_pureconj : forall P Q R, ( P //\\ Q ) ** R = P //\\ ( Q ** R ) .
Proof.
   intros P Q R. rewrite <- ! pureconj_sepconj. custom5 sepconj_assoc.
Qed.
Lemma lift_aexists : forall ( A : Type ) ( P : A -> assertion ) Q, aexists P ** Q = aexists ( fun x => P x ** Q ) .
Proof.
   custom6 A P Q assertion_extensionality h.
    - intros ( h1 & h2 & ( a & P1 ) & Q2 & DISJ & EQ ). exists a, h1, h2. auto.
    - intros ( a & h1 & h2 & P1 & Q2 & DISJ & EQ ). custom7 h1 h2. exists a. auto.
Qed.
Lemma sepconj_swap3 : forall R P Q, P ** Q ** R = R ** P ** Q .
Proof.
   intros R P Q. rewrite <- sepconj_assoc, sepconj_comm. auto.
Qed.
Lemma sepconj_swap4 : forall S P Q R, P ** Q ** R ** S = S ** P ** Q ** R .
Proof.
   intros S P Q R. rewrite <- sepconj_assoc, sepconj_swap3, sepconj_assoc. auto.
Qed.
Lemma sepconj_pick2 : forall Q P R, P ** Q ** R = Q ** P ** R .
Proof.
   intros Q P R. rewrite ( sepconj_comm Q ), <- sepconj_assoc, sepconj_comm. auto.
Qed.
Lemma sepconj_pick3 : forall R P Q S, P ** Q ** R ** S = R ** P ** Q ** S .
Proof.
   custom31 R P Q S sepconj_pick2 sepconj_pick2. auto.
Qed.
Lemma wand_intro : forall P Q R, P ** Q -->> R -> P -->> Q --* R .
Proof.
   intros P Q R IMP h Ph h' DISJ Qh'. custom13 IMP h h'.
Qed.
Lemma wand_cancel : forall P Q, P ** ( P --* Q ) -->> Q .
Proof.
   custom28 P Q h h1 h2 Ph1 Wh2 D U. assert ( D' : hdisjoint h2 h1 ) by ( apply hdisjoint_sym ; auto ). rewrite hunion_comm by auto. custom14 Wh2.
Qed.
Lemma wand_charact : forall P Q, ( P --* Q ) = ( aexists ( fun R => ( P ** R -->> Q ) //\\ R ) ) .
Proof.
   custom17 P Q assertion_extensionality h. custom19 W.
    - exists ( P --* Q ). split.
      -- apply wand_cancel.
      -- auto.
    - intros ( R & A & B ) h' D Ph'. assert ( D' : hdisjoint h' h ) by ( apply hdisjoint_sym ; auto ). rewrite hunion_comm by auto. custom13 A h' h.
Qed.
Lemma wand_equiv : forall P Q R, ( P -->> ( Q --* R ) ) <-> ( P ** Q -->> R ) .
Proof.
   custom33 P Q R H.
    - custom27 h h1 h2 Ph1 Wh2 D U. custom14 H. auto.
    - intros H. custom4 wand_intro.
Qed.
Lemma wand_imp_l : forall P P' Q, ( P' -->> P ) -> ( P --* Q -->> P' --* Q ) .
Proof.
   custom30 P P' Q H h W h' DISJ P'h'. custom14 W.
Qed.
Lemma wand_imp_r : forall P Q Q', ( Q -->> Q' ) -> ( P --* Q -->> P --* Q' ) .
Proof.
   custom30 P Q Q' H h W h' DISJ Ph'. apply H. custom14 W.
Qed.
Lemma wand_idem : forall P, emp -->> P --* P .
Proof.
   intros P h E. rewrite E. red. intros h' H H0. custom5 hunion_empty.
Qed.
Lemma wand_pure_l : forall ( P : Prop ) Q, P -> ( pure P --* Q ) = Q .
Proof.
   custom6 P Q PP assertion_extensionality h.
    - intros W. rewrite <- hunion_empty, hunion_comm by HDISJ. custom9 W. custom15.
    - intros Qh h' DISJ ( Ph' & E ). subst h'. rewrite hunion_comm, hunion_empty by HDISJ. auto.
Qed.
Lemma wand_curry : forall P Q R, ( P ** Q --* R ) = ( P --* Q --* R ) .
Proof.
   custom6 P Q R assertion_extensionality h.
    - intros W h1 D1 Ph1 h2 D2 Qh2. rewrite hunion_assoc. custom9 W. custom7 h1 h2. HDISJ.
    - intros W h' D ( h1 & h2 & Ph1 & Qh2 & D12 & U12 ). subst h'. rewrite <- hunion_assoc. custom26 W.
      -- HDISJ.
      -- auto.
Qed.
Lemma wand_star : forall P Q R, ( ( P --* Q ) ** R ) -->> ( P --* ( Q ** R ) ) .
Proof.
   intros P Q R. custom27 h h1 h2 W1 R2 D U. intros h' D' Ph'. exists ( hunion h1 h' ), h2. intuition auto.
    - custom26 W1.
    - HDISJ.
    - rewrite ! hunion_assoc. f_equal. custom9 hunion_comm.
Qed.
Remark param_precise_precise : forall ( X : Type ) ( P : X -> assertion ), param_precise P -> forall x, precise ( P x ) .
Proof.
   intros X P H x. custom18 h1 h2 h1' h2' H0 H1 H2 H3 H4. edestruct ( H x x h1 h2 h1' h2' ) as [  | | | | | H6 H5 ].
    - eauto.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
Qed.
Remark precise_param_precise : forall P, precise P -> param_precise ( fun _ : unit => P ) .
Proof.
   intros P H. custom12 x1 x2 h1 h2 h1' h2' H0 H1 H2 H3 H4.
    - destruct x1, x2 as [  ]. auto.
    - eauto.
Qed.
Lemma pure_precise : forall P, precise ( pure P ) .
Proof.
   unfold pure. intros P. custom18 h1 h2 h1' h2' H H0 H1 H2 H3. custom22 H2 H3.
Qed.
Lemma pure_param_precise : forall ( X : Type ) ( P : X -> Prop ), ( forall x1 x2, P x1 -> P x2 -> x1 = x2 ) -> param_precise ( fun x => pure ( P x ) ) .
Proof.
   unfold pure. intros X P H. custom12 x1 x2 h1 h2 h1' h2' H0 H1 H2 H3 H4.
    - auto.
    - destruct H3, H4 as [  H6 H4 H5 H3 ]. custom22 H3 H4.
Qed.
Lemma contains_param_precise : forall l, param_precise ( fun v => contains l v ) .
Proof.
   unfold contains. intros l. red. intros x1 x2 h1 h2 h1' h2' H H0 H1 H2 H3. assert ( E : hunion h1 h2 l = hunion h1' h2' l ) by congruence. cbn in E. subst h1 h1'. rewrite ! hupdate_same in E. replace x2 with x1 by congruence. auto.
Qed.
Lemma contains_precise : forall l v, precise ( contains l v ) .
Proof.
   intros l v. custom25 param_precise_precise contains_param_precise.
Qed.
Lemma aexists_precise : forall ( X : Type ) ( P : X -> assertion ), param_precise P -> precise ( aexists P ) .
Proof.
   intros X P H. custom18 h1 h2 h1' h2' H0 H1 H2 H3 H4. destruct H3 as ( x1 & P1 ), H4 as ( x2 & P2 ). eapply H.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
Qed.
Lemma valid_precise : forall l, precise ( valid l ) .
Proof.
   intros l. custom25 aexists_precise contains_param_precise.
Qed.
Lemma sepconj_param_precise : forall ( X : Type ) ( P Q : X -> assertion ), param_precise P -> ( forall x, precise ( Q x ) ) -> param_precise ( fun x => P x ** Q x ) .
Proof.
   intros X P Q H H0. red. intros x1 x2 h1 h2 h1' h2' H1 H2 H3 H4 H5. destruct H4 as ( h3 & h4 & P3 & Q4 & D & E ). destruct H5 as ( h3' & h4' & P3' & Q4' & D' & E' ). subst h1 h1'. assert ( x1 = x2 /\ h3 = h3' ).
    - apply H with ( hunion h4 h2 ) ( hunion h4' h2' ).
      -- HDISJ.
      -- HDISJ.
      -- rewrite <- ! hunion_assoc. auto.
      -- auto.
      -- auto.
    - destruct H4 as [  H5 H4 ]. subst x2. assert ( h4 = h4' ).
      -- apply ( H0 x1 ) with ( hunion h3 h2 ) ( hunion h3' h2' ).
        --- HDISJ.
        --- HDISJ.
        --- rewrite <- ! hunion_assoc. rewrite ( hunion_comm h3 ) by HDISJ. rewrite ( hunion_comm h3' ) by HDISJ. auto.
        --- auto.
        --- auto.
      -- subst h3 h4. auto.
Qed.
Lemma sepconj_precise : forall P Q, precise P -> precise Q -> precise ( P ** Q ) .
Proof.
   intros P Q H H0. assert ( param_precise ( fun _ : unit => P ** Q ) ).
    - apply sepconj_param_precise.
      -- custom4 precise_param_precise.
      -- auto.
    - apply param_precise_precise in H1.
      -- auto.
      -- exact tt.
Qed.
Lemma sepconj_and_distr_1 : forall P1 P2 Q, aand P1 P2 ** Q -->> aand ( P1 ** Q ) ( P2 ** Q ) .
Proof.
   intros P1 P2 Q h ( h1 & h2 & ( P11 & P21 ) & Q2 & D & E ). split.
    - custom24 h1 h2.
    - custom24 h1 h2.
Qed.
Lemma sepconj_and_distr_2 : forall P1 P2 Q, precise Q -> aand ( P1 ** Q ) ( P2 ** Q ) -->> aand P1 P2 ** Q .
Proof.
   custom31 P1 P2 Q PQ sepconj_comm sepconj_comm. intros h ( ( h1 & h2 & Q1 & P12 & D & E ) & ( h1' & h2' & Q1' & P22 & D' & E' ) ). custom2 h1 h1' PQ h2 h2' h2.
    - auto.
    - congruence.
    - apply hunion_invert_r with h1.
      -- congruence.
      -- auto.
      -- auto.
    - subst h2'. unfold aand. custom7 h2 h1.
      -- HDISJ.
      -- rewrite hunion_comm by HDISJ. auto.
Qed.
Lemma sepconj_self : forall P, precise P -> P ** P -->> P .
Proof.
   intros P H. intros h ( h1 & h2 & P1 & P2 & D & E ). custom2 h1 h2 H h2 h1 h.
    - HDISJ.
    - custom9 hunion_comm.
    - custom0 heap_extensionality l. rewrite E. custom8 h1 l.
    - congruence.
Qed.

Ltac custom0 H0 H1 :=  apply H0; [intros H1 | .. ].
Ltac custom1 H0 H1 H3 H4 H5 H6 H7 H8 H2 :=  intros H0 H1; [induction H1; [intros H3 H4 H5; [cbn | .. ] | intros H6 H7 H8; [cbn; [destruct ( Z.eq_dec H6 H7 ); [ | apply H2 | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom2 H0 H1 H3 H4 H5 H14 :=  assert ( H0 = H1 ); [apply H3 with H4 H5; [auto |  |  | auto | auto | .. ] | subst H1; [assert ( H14 = H5 )] | .. ].
Ltac custom3 H0 H1 H9 H7 H17 :=  rewrite H0 in H1; [intuition auto; [exists H9, H7; [intuition auto | .. ] | rewrite H17; [tauto | .. ] | .. ] | .. ].
Ltac custom4 H0 :=  apply H0; [auto | .. ].
Ltac custom5 H0 :=  rewrite H0; [auto | .. ].
Ltac custom6 H0 H1 H2 H3 H4 :=  intros H0 H1 H2; [custom0 H3 H4; [split | .. ] | .. ].
Ltac custom7 H0 H1 :=  exists H0, H1; [intuition auto | .. ].
Ltac custom8 H0 H1 :=  cbn; [destruct ( H0 H1 ) as [ z| ]; [auto | auto | .. ] | .. ].
Ltac custom9 H0 :=  apply H0; [HDISJ | .. ].
Ltac custom10 H4 H5 :=  intuition; [intro H4; [auto | .. ] | custom5 H5 | .. ].
Ltac custom11 H0 H1 H2 :=  intros H0; [destruct ( H1 H0 ) as [ z| ]; [destruct ( H2 H0 ) as [ z'| ] | auto | .. ] | .. ].
Ltac custom12 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 :=  red; [intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10; [split | .. ] | .. ].
Ltac custom13 H0 H1 H2 :=  apply H0; [exists H1, H2; [auto | .. ] | .. ].
Ltac custom14 H0 :=  custom4 H0; [auto | .. ].
Ltac custom15  :=  split; [auto | auto | .. ].
Ltac custom16 H0 H1 :=  intros H0 H1; [specialize ( H0 H1 ); [tauto] | .. ].
Ltac custom17 H0 H1 H2 H3 :=  intros H0 H1; [custom0 H2 H3 | .. ].
Ltac custom18 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  red; [intros H0 H1 H2 H3 H4 H5 H6 H7 H8 | .. ].
Ltac custom19 H0 :=  split; [intros H0 | .. ].
Ltac custom20 H0 H1 H2 H3 H4 :=  intros H0 H1 H2; [custom0 H3 H4 | .. ].
Ltac custom21  :=  red; [auto | .. ].
Ltac custom22 H0 H1 :=  destruct H0, H1; [congruence].
Ltac custom23 H0 H5 :=  cbn; [destruct ( Z.eq_dec H0 H5 ) | .. ].
Ltac custom24 H0 H1 :=  exists H0, H1; [auto | .. ].
Ltac custom25 H0 H1 :=  apply H0; [apply H1 | .. ].
Ltac custom26 H0 :=  custom9 H0; [auto | .. ].
Ltac custom27 H0 H1 H2 H3 H4 H5 H6 :=  intros H0 ( H1 & H2 & H3 & H4 & H5 & H6 ); [subst H0 | .. ].
Ltac custom28 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1 H2 ( H3 & H4 & H5 & H6 & H7 & H8 ); [subst H2 | .. ].
Ltac custom29 H0 H1 H2 :=  intros H0 H1; [destruct ( Z.eq_dec H2 H0 ) | .. ].
Ltac custom30 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1 H2 H3; [intros H4 H5 H6 H7 H8 | .. ].
Ltac custom31 H0 H1 H2 H3 H4 H5 :=  intros H0 H1 H2 H3; [rewrite ( H4 H0 ), ( H5 H1 ) | .. ].
Ltac custom32 H0 H1 H5 :=  subst H0 H1; [custom5 H5 | .. ].
Ltac custom33 H0 H1 H2 H3 :=  intros H0 H1 H2; [custom19 H3 | .. ].
