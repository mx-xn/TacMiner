Require Import Coqlib.

Require Errors.

Require Import Maps.

Require Import AST.

Require Import Integers.

Require Import Switch.

Require Import Op.

Require Import Registers.

Require Import CminorSel.

Require Import RTL.

Require Import RTLgen.

Require Import Dependencies.

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: state) (i: state_incr s1 s3),
  bind f g s1 = OK y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof. intros until i. unfold bind. destruct (f s1); intros. discriminate. exists a; exists s'; exists s. destruct (g a s'); inv H. exists s0; auto. Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: state) (i: state_incr s1 s3),
  bind2 f g s1 = OK z s3 i ->
  exists x, exists y, exists s2, exists i1, exists i2,
  f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
Proof. unfold bind2; intros. exploit bind_inversion; eauto. intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q. exists x; exists y; exists s2; exists i1; exists i2; auto. Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
      discriminate
  | (ret _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Global Hint Resolve state_incr_refl: rtlg.

Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> s2.(st_code)!n = Some i.
Proof. intros. inv H. destruct (H3 n); congruence. Qed.

Global Hint Resolve instr_at_incr: rtlg.

Ltac saturateTrans :=
  match goal with
  | H1: state_incr ?x ?y, H2: state_incr ?y ?z |- _ =>
      match goal with
      | H: state_incr x z |- _  =>
         fail 1
      | _ =>
         let i := fresh "INCR" in
         (generalize (state_incr_trans x y z H1 H2); intro i;
          saturateTrans)
      end
  | _ => idtac
  end.

Definition reg_valid (r: reg) (s: state) : Prop :=
  Plt r s.(st_nextreg).

Definition reg_fresh (r: reg) (s: state) : Prop :=
  ~(Plt r s.(st_nextreg)).

Lemma valid_fresh_absurd:
  forall r s, reg_valid r s -> reg_fresh r s -> False.
Proof. intros r s. unfold reg_valid, reg_fresh; case r; tauto. Qed.

Global Hint Resolve valid_fresh_absurd: rtlg.

Lemma valid_fresh_different:
  forall r1 r2 s, reg_valid r1 s -> reg_fresh r2 s -> r1 <> r2.
Proof. unfold not; intros. subst r2. eauto with rtlg. Qed.

Global Hint Resolve valid_fresh_different: rtlg.

Lemma reg_valid_incr:
  forall r s1 s2, state_incr s1 s2 -> reg_valid r s1 -> reg_valid r s2.
Proof. intros r s1 s2 INCR. inversion INCR. unfold reg_valid. intros; apply Plt_Ple_trans with (st_nextreg s1); auto. Qed.

Global Hint Resolve reg_valid_incr: rtlg.

Lemma reg_fresh_decr:
  forall r s1 s2, state_incr s1 s2 -> reg_fresh r s2 -> reg_fresh r s1.
Proof. intros r s1 s2 INCR. inversion INCR. unfold reg_fresh; unfold not; intros. apply H4. apply Plt_Ple_trans with (st_nextreg s1); auto. Qed.

Global Hint Resolve reg_fresh_decr: rtlg.

Definition regs_valid (rl: list reg) (s: state) : Prop :=
  forall r, In r rl -> reg_valid r s.

Lemma regs_valid_nil:
  forall s, regs_valid nil s.
Proof. intros; red; intros. elim H. Qed.

Global Hint Resolve regs_valid_nil: rtlg.

Lemma regs_valid_cons:
  forall r1 rl s,
  reg_valid r1 s -> regs_valid rl s -> regs_valid (r1 :: rl) s.
Proof. intros; red; intros. elim H1; intro. subst r1; auto. auto. Qed.

Lemma regs_valid_app:
  forall rl1 rl2 s,
  regs_valid rl1 s -> regs_valid rl2 s -> regs_valid (rl1 ++ rl2) s.
Proof. intros; red; intros. apply in_app_iff in H1. destruct H1; auto. Qed.

Lemma regs_valid_incr:
  forall s1 s2 rl, state_incr s1 s2 -> regs_valid rl s1 -> regs_valid rl s2.
Proof. unfold regs_valid; intros; eauto with rtlg. Qed.

Global Hint Resolve regs_valid_incr: rtlg.

Definition reg_in_map (m: mapping) (r: reg) : Prop :=
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

Definition map_valid (m: mapping) (s: state) : Prop :=
  forall r, reg_in_map m r -> reg_valid r s.

Lemma map_valid_incr:
  forall s1 s2 m,
  state_incr s1 s2 -> map_valid m s1 -> map_valid m s2.
Proof. unfold map_valid; intros; eauto with rtlg. Qed.

Global Hint Resolve map_valid_incr: rtlg.

Lemma add_instr_at:
  forall s1 s2 incr i n,
  add_instr i s1 = OK n s2 incr -> s2.(st_code)!n = Some i.
Proof. intros. monadInv H. simpl. apply PTree.gss. Qed.

Global Hint Resolve add_instr_at: rtlg.

Lemma update_instr_at:
  forall n i s1 s2 incr u,
  update_instr n i s1 = OK u s2 incr -> s2.(st_code)!n = Some i.
Proof. intros. unfold update_instr in H. destruct (plt n (st_nextnode s1)); try discriminate. destruct (check_empty_node s1 n); try discriminate. inv H. simpl. apply PTree.gss. Qed.

Global Hint Resolve update_instr_at: rtlg.

Lemma new_reg_valid:
  forall s1 s2 r i,
  new_reg s1 = OK r s2 i -> reg_valid r s2.
Proof. intros. monadInv H. unfold reg_valid; simpl. apply Plt_succ. Qed.

Global Hint Resolve new_reg_valid: rtlg.

Lemma new_reg_fresh:
  forall s1 s2 r i,
  new_reg s1 = OK r s2 i -> reg_fresh r s1.
Proof. intros. monadInv H. unfold reg_fresh; simpl. exact (Plt_strict _). Qed.

Global Hint Resolve new_reg_fresh: rtlg.

Lemma new_reg_not_in_map:
  forall s1 s2 m r i,
  new_reg s1 = OK r s2 i -> map_valid m s1 -> ~(reg_in_map m r).
Proof. unfold not; intros; eauto with rtlg. Qed.

Global Hint Resolve new_reg_not_in_map: rtlg.

Lemma init_mapping_valid:
  forall s, map_valid init_mapping s.
Proof. unfold map_valid, init_mapping. intros s r [[id A] | B]. simpl in A. rewrite PTree.gempty in A; discriminate. simpl in B. tauto. Qed.

Lemma find_var_in_map:
  forall s1 s2 map name r i,
  find_var map name s1 = OK r s2 i -> reg_in_map map r.
Proof. intros until r. unfold find_var; caseEq (map.(map_vars)!name). intros. inv H0. left; exists name; auto. intros. inv H0. Qed.

Global Hint Resolve find_var_in_map: rtlg.

Lemma find_var_valid:
  forall s1 s2 map name r i,
  find_var map name s1 = OK r s2 i -> map_valid map s1 -> reg_valid r s1.
Proof. intros. eauto with rtlg. Qed.

Global Hint Resolve find_var_valid: rtlg.

Lemma find_letvar_in_map:
  forall s1 s2 map idx r i,
  find_letvar map idx s1 = OK r s2 i -> reg_in_map map r.
Proof. intros until r. unfold find_letvar. caseEq (nth_error (map_letvars map) idx); intros; monadInv H0. right; apply nth_error_in with idx; auto. Qed.

Global Hint Resolve find_letvar_in_map: rtlg.

Lemma find_letvar_valid:
  forall s1 s2 map idx r i,
  find_letvar map idx s1 = OK r s2 i -> map_valid map s1 -> reg_valid r s1.
Proof. intros. eauto with rtlg. Qed.

Global Hint Resolve find_letvar_valid: rtlg.

Lemma add_var_valid:
  forall s1 s2 map1 map2 name r i,
  add_var map1 name s1 = OK (r, map2) s2 i ->
  map_valid map1 s1 ->
  reg_valid r s2 /\ map_valid map2 s2.
Proof. intros. monadInv H. split. eauto with rtlg. inversion EQ. subst r s2. red. intros r' [[id A] | B]. simpl in A. rewrite PTree.gsspec in A. destruct (peq id name). inv A. eauto with rtlg. apply reg_valid_incr with s1. eauto with rtlg. apply H0. left; exists id; auto. simpl in B. apply reg_valid_incr with s1. eauto with rtlg. apply H0. right; auto. Qed.

Lemma add_var_find:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i -> map'.(map_vars)!name = Some r.
Proof. intros. monadInv H. simpl. apply PTree.gss. Qed.

Lemma add_vars_valid:
  forall namel s1 s2 map1 map2 rl i,
  add_vars map1 namel s1 = OK (rl, map2) s2 i ->
  map_valid map1 s1 ->
  regs_valid rl s2 /\ map_valid map2 s2.
Proof. intro namel. induction namel; simpl; intros; monadInv H. split. red; simpl; intros; tauto. auto. exploit IHnamel; eauto. intros [A B]. exploit add_var_valid; eauto. intros [C D]. split. apply regs_valid_cons; eauto with rtlg. auto. Qed.

Lemma add_var_letenv:
  forall map1 id s1 r map2 s2 i,
  add_var map1 id s1 = OK (r, map2) s2 i ->
  map2.(map_letvars) = map1.(map_letvars).
Proof. intros; monadInv H. reflexivity. Qed.

Lemma add_vars_letenv:
  forall il map1 s1 rl map2 s2 i,
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  map2.(map_letvars) = map1.(map_letvars).
Proof. intro il. induction il; simpl; intros; monadInv H. reflexivity. transitivity (map_letvars x0). eapply add_var_letenv; eauto. eauto. Qed.

Lemma add_letvar_valid:
  forall map s r,
  map_valid map s ->
  reg_valid r s ->
  map_valid (add_letvar map r) s.
Proof. intros; red; intros. destruct H1 as [[id A]|B]. simpl in A. apply H. left; exists id; auto. simpl in B. elim B; intro. subst r0; auto. apply H. right; auto. Qed.

Lemma alloc_reg_valid:
  forall a s1 s2 map r i,
  map_valid map s1 ->
  alloc_reg map a s1 = OK r s2 i -> reg_valid r s2.
Proof. intros until r. unfold alloc_reg. case a; eauto with rtlg. Qed.

Global Hint Resolve alloc_reg_valid: rtlg.

Lemma alloc_reg_fresh_or_in_map:
  forall map a s r s' i,
  map_valid map s ->
  alloc_reg map a s = OK r s' i ->
  reg_in_map map r \/ reg_fresh r s.
Proof. intros until s'. unfold alloc_reg. destruct a; intros; try (right; eauto with rtlg; fail). left; eauto with rtlg. left; eauto with rtlg. Qed.

Lemma alloc_regs_valid:
  forall al s1 s2 map rl i,
  map_valid map s1 ->
  alloc_regs map al s1 = OK rl s2 i ->
  regs_valid rl s2.
Proof. intro al. induction al; simpl; intros; monadInv H0. apply regs_valid_nil. apply regs_valid_cons. eauto with rtlg. eauto with rtlg. Qed.

Global Hint Resolve alloc_regs_valid: rtlg.

Lemma alloc_regs_fresh_or_in_map:
  forall map al s rl s' i,
  map_valid map s ->
  alloc_regs map al s = OK rl s' i ->
  forall r, In r rl -> reg_in_map map r \/ reg_fresh r s.
Proof. intros map al. induction al; simpl; intros; monadInv H0. elim H1. elim H1; intro. subst r. eapply alloc_reg_fresh_or_in_map; eauto. exploit IHal. 2: eauto. apply map_valid_incr with s; eauto with rtlg. eauto. intros [A|B]. auto. right; eauto with rtlg. Qed.

Lemma alloc_optreg_valid:
  forall dest s1 s2 map r i,
  map_valid map s1 ->
  alloc_optreg map dest s1 = OK r s2 i -> reg_valid r s2.
Proof. intros until r. unfold alloc_reg. case dest; eauto with rtlg. Qed.

Global Hint Resolve alloc_optreg_valid: rtlg.

Lemma alloc_optreg_fresh_or_in_map:
  forall map dest s r s' i,
  map_valid map s ->
  alloc_optreg map dest s = OK r s' i ->
  reg_in_map map r \/ reg_fresh r s.
Proof. intros until s'. unfold alloc_optreg. destruct dest; intros. left; eauto with rtlg. right; eauto with rtlg. Qed.

Inductive target_reg_ok (map: mapping) (pr: list reg): expr -> reg -> Prop :=
  | target_reg_var:
      forall id r,
      map.(map_vars)!id = Some r ->
      target_reg_ok map pr (Evar id) r
  | target_reg_letvar:
      forall idx r,
      nth_error map.(map_letvars) idx = Some r ->
      target_reg_ok map pr (Eletvar idx) r
  | target_reg_other:
      forall a r,
      ~(reg_in_map map r) -> ~In r pr ->
      target_reg_ok map pr a r.

Inductive target_regs_ok (map: mapping) (pr: list reg): exprlist -> list reg -> Prop :=
  | target_regs_nil:
      target_regs_ok map pr Enil nil
  | target_regs_cons: forall a1 al r1 rl,
      target_reg_ok map pr a1 r1 ->
      target_regs_ok map (r1 :: pr) al rl ->
      target_regs_ok map pr (Econs a1 al) (r1 :: rl).

Lemma target_reg_ok_append:
  forall map pr a r,
  target_reg_ok map pr a r ->
  forall pr',
  (forall r', In r' pr' -> reg_in_map map r' \/ r' <> r) ->
  target_reg_ok map (pr' ++ pr) a r.
Proof. induction 1; intros. constructor; auto. constructor; auto. constructor; auto. red; intros. elim (in_app_or _ _ _ H2); intro. generalize (H1 _ H3). tauto. tauto. Qed.

Lemma target_reg_ok_cons:
  forall map pr a r,
  target_reg_ok map pr a r ->
  forall r',
  reg_in_map map r' \/ r' <> r ->
  target_reg_ok map (r' :: pr) a r.
Proof. intros. change (r' :: pr) with ((r' :: nil) ++ pr). apply target_reg_ok_append; auto. intros r'' [A|B]. subst r''; auto. contradiction. Qed.

Lemma new_reg_target_ok:
  forall map pr s1 a r s2 i,
  map_valid map s1 ->
  regs_valid pr s1 ->
  new_reg s1 = OK r s2 i ->
  target_reg_ok map pr a r.
Proof. intros. constructor. red; intro. apply valid_fresh_absurd with r s1. eauto with rtlg. eauto with rtlg. red; intro. apply valid_fresh_absurd with r s1. auto. eauto with rtlg. Qed.

Lemma alloc_reg_target_ok:
  forall map pr s1 a r s2 i,
  map_valid map s1 ->
  regs_valid pr s1 ->
  alloc_reg map a s1 = OK r s2 i ->
  target_reg_ok map pr a r.
Proof. intros. unfold alloc_reg in H1. destruct a; try (eapply new_reg_target_ok; eauto; fail). generalize H1; unfold find_var. caseEq (map_vars map)!i0; intros. inv H3. constructor. auto. inv H3. generalize H1; unfold find_letvar. caseEq (nth_error (map_letvars map) n); intros. inv H3. constructor. auto. inv H3. Qed.

Lemma alloc_regs_target_ok:
  forall map al pr s1 rl s2 i,
  map_valid map s1 ->
  regs_valid pr s1 ->
  alloc_regs map al s1 = OK rl s2 i ->
  target_regs_ok map pr al rl.
Proof. intros map al. induction al; intros; monadInv H1. constructor. constructor. eapply alloc_reg_target_ok; eauto. apply IHal with s s2 INCR1; eauto with rtlg. apply regs_valid_cons; eauto with rtlg. Qed.

Global Hint Resolve new_reg_target_ok alloc_reg_target_ok
             alloc_regs_target_ok: rtlg.

Inductive return_reg_ok: state -> mapping -> option reg -> Prop :=
  | return_reg_ok_none:
      forall s map,
      return_reg_ok s map None
  | return_reg_ok_some:
      forall s map r,
      ~(reg_in_map map r) -> reg_valid r s ->
      return_reg_ok s map (Some r).

Lemma return_reg_ok_incr:
  forall s map rret, return_reg_ok s map rret ->
  forall s', state_incr s s' -> return_reg_ok s' map rret.
Proof. induction 1; intros; econstructor; eauto with rtlg. Qed.

Global Hint Resolve return_reg_ok_incr: rtlg.

Lemma new_reg_return_ok:
  forall s1 r s2 map sig i,
  new_reg s1 = OK r s2 i ->
  map_valid map s1 ->
  return_reg_ok s2 map (ret_reg sig r).
Proof. intros. unfold ret_reg. destruct (xtype_eq (sig_res sig) Xvoid); constructor; eauto with rtlg. Qed.

Inductive tr_move (c: code):
       node -> reg -> node -> reg -> Prop :=
  | tr_move_0: forall n r,
      tr_move c n r n r
  | tr_move_1: forall ns rs nd rd,
      c!ns = Some (Iop Omove (rs :: nil) rd nd) ->
      tr_move c ns rs nd rd.

Inductive reg_map_ok: mapping -> reg -> option ident -> Prop :=
  | reg_map_ok_novar: forall map rd,
      ~reg_in_map map rd ->
      reg_map_ok map rd None
  | reg_map_ok_somevar: forall map rd id,
      map.(map_vars)!id = Some rd ->
      reg_map_ok map rd (Some id).

Global Hint Resolve reg_map_ok_novar: rtlg.

Inductive tr_expr (c: code):
       mapping -> list reg -> expr -> node -> node -> reg -> option ident -> Prop :=
  | tr_Evar: forall map pr id ns nd r rd dst,
      map.(map_vars)!id = Some r ->
      ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
      tr_move c ns r nd rd ->
      tr_expr c map pr (Evar id) ns nd rd dst
  | tr_Eop: forall map pr op al ns nd rd n1 rl dst,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Iop op rl rd nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (Eop op al) ns nd rd dst
  | tr_Eload: forall map pr chunk addr al ns nd rd n1 rl dst,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Iload chunk addr rl rd nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (Eload chunk addr al) ns nd rd dst
  | tr_Econdition: forall map pr a ifso ifnot ns nd rd ntrue nfalse dst,
      tr_condition c map pr a ns ntrue nfalse ->
      tr_expr c map pr ifso ntrue nd rd dst ->
      tr_expr c map pr ifnot nfalse nd rd dst ->
      tr_expr c map pr (Econdition a ifso ifnot) ns nd rd dst
  | tr_Elet: forall map pr b1 b2 ns nd rd n1 r dst,
      ~reg_in_map map r ->
      tr_expr c map pr b1 ns n1 r None ->
      tr_expr c (add_letvar map r) pr b2 n1 nd rd dst ->
      tr_expr c map pr (Elet b1 b2) ns nd rd dst
  | tr_Eletvar: forall map pr n ns nd rd r dst,
      List.nth_error map.(map_letvars) n = Some r ->
      ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
      tr_move c ns r nd rd ->
      tr_expr c map pr (Eletvar n) ns nd rd dst
  | tr_Ebuiltin: forall map pr ef al ns nd rd dst n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Ibuiltin ef (List.map (@BA reg) rl) (BR rd) nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (Ebuiltin ef al) ns nd rd dst
  | tr_Eexternal: forall map pr id sg al ns nd rd dst n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Icall sg (inr _ id) rl rd nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (Eexternal id sg al) ns nd rd dst




with tr_condition (c: code):
       mapping -> list reg -> condexpr -> node -> node -> node -> Prop :=
  | tr_CEcond: forall map pr cond bl ns ntrue nfalse n1 rl,
      tr_exprlist c map pr bl ns n1 rl ->
      c!n1 = Some (Icond cond rl ntrue nfalse) ->
      tr_condition c map pr (CEcond cond bl) ns ntrue nfalse
  | tr_CEcondition: forall map pr a1 a2 a3 ns ntrue nfalse n2 n3,
      tr_condition c map pr a1 ns n2 n3 ->
      tr_condition c map pr a2 n2 ntrue nfalse ->
      tr_condition c map pr a3 n3 ntrue nfalse ->
      tr_condition c map pr (CEcondition a1 a2 a3) ns ntrue nfalse
  | tr_CElet: forall map pr a b ns ntrue nfalse r n1,
      ~reg_in_map map r ->
      tr_expr c map pr a ns n1 r None ->
      tr_condition c (add_letvar map r) pr b n1 ntrue nfalse ->
      tr_condition c map pr (CElet a b) ns ntrue nfalse



with tr_exprlist (c: code):
       mapping -> list reg -> exprlist -> node -> node -> list reg -> Prop :=
  | tr_Enil: forall map pr n,
      tr_exprlist c map pr Enil n n nil
  | tr_Econs: forall map pr a1 al ns nd r1 rl n1,
      tr_expr c map pr a1 ns n1 r1 None ->
      tr_exprlist c map (r1 :: pr) al n1 nd rl ->
      tr_exprlist c map pr (Econs a1 al) ns nd (r1 :: rl).

Definition tr_jumptable (nexits: list node) (tbl: list nat) (ttbl: list node) : Prop :=
  forall v act,
  list_nth_z tbl v = Some act ->
  exists n, list_nth_z ttbl v = Some n /\ nth_error nexits act = Some n.

Inductive tr_exitexpr (c: code):
       mapping -> exitexpr -> node -> list node -> Prop :=
  | tr_XEcond: forall map x n nexits,
      nth_error nexits x = Some n ->
      tr_exitexpr c map (XEexit x) n nexits
  | tr_XEjumptable: forall map a tbl ns nexits n1 r tbl',
      tr_jumptable nexits tbl tbl' ->
      tr_expr c map nil a ns n1 r None ->
      c!n1 = Some (Ijumptable r tbl') ->
      tr_exitexpr c map (XEjumptable a tbl) ns nexits
  | tr_XEcondition: forall map a1 a2 a3 ns nexits n2 n3,
      tr_condition c map nil a1 ns n2 n3 ->
      tr_exitexpr c map a2 n2 nexits ->
      tr_exitexpr c map a3 n3 nexits ->
      tr_exitexpr c map (XEcondition a1 a2 a3) ns nexits
  | tr_XElet: forall map a b ns nexits r n1,
      ~reg_in_map map r ->
      tr_expr c map nil a ns n1 r None ->
      tr_exitexpr c (add_letvar map r) b n1 nexits ->
      tr_exitexpr c map (XElet a b) ns nexits.

Inductive tr_builtin_res: mapping -> builtin_res ident -> builtin_res reg -> Prop :=
  | tr_builtin_res_var: forall map id r,
      map.(map_vars)!id = Some r ->
      tr_builtin_res map (BR id) (BR r)
  | tr_builtin_res_none: forall map,
      tr_builtin_res map BR_none BR_none
  | tr_builtin_res_fresh: forall map r,
      ~reg_in_map map r ->
      tr_builtin_res map BR_none (BR r).

Inductive tr_stmt (c: code) (map: mapping):
     stmt -> node -> node -> list node -> labelmap -> node -> option reg -> Prop :=
  | tr_Sskip: forall ns nexits ngoto nret rret,
     tr_stmt c map Sskip ns ns nexits ngoto nret rret
  | tr_Sassign: forall id a ns nd nexits ngoto nret rret r,
     map.(map_vars)!id = Some r ->
     tr_expr c map nil a ns nd r (Some id) ->
     tr_stmt c map (Sassign id a) ns nd nexits ngoto nret rret
  | tr_Sstore: forall chunk addr al b ns nd nexits ngoto nret rret rd n1 rl n2,
     tr_exprlist c map nil al ns n1 rl ->
     tr_expr c map rl b n1 n2 rd None ->
     c!n2 = Some (Istore chunk addr rl rd nd) ->
     tr_stmt c map (Sstore chunk addr al b) ns nd nexits ngoto nret rret
  | tr_Scall: forall optid sig b cl ns nd nexits ngoto nret rret rd n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf None ->
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs ->
     c!n2 = Some (Icall sig (inl _ rf) rargs rd nd) ->
     reg_map_ok map rd optid ->
     tr_stmt c map (Scall optid sig (inl _ b) cl) ns nd nexits ngoto nret rret
  | tr_Scall_imm: forall optid sig id cl ns nd nexits ngoto nret rret rd n2 rargs,
     tr_exprlist c map nil cl ns n2 rargs ->
     c!n2 = Some (Icall sig (inr _ id) rargs rd nd) ->
     reg_map_ok map rd optid ->
     tr_stmt c map (Scall optid sig (inr _ id) cl) ns nd nexits ngoto nret rret
  | tr_Stailcall: forall sig b cl ns nd nexits ngoto nret rret n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf None ->
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs ->
     c!n2 = Some (Itailcall sig (inl _ rf) rargs) ->
     tr_stmt c map (Stailcall sig (inl _ b) cl) ns nd nexits ngoto nret rret
  | tr_Stailcall_imm: forall sig id cl ns nd nexits ngoto nret rret n2 rargs,
     tr_exprlist c map nil cl ns n2 rargs ->
     c!n2 = Some (Itailcall sig (inr _ id) rargs) ->
     tr_stmt c map (Stailcall sig (inr _ id) cl) ns nd nexits ngoto nret rret
  | tr_Sbuiltin: forall res ef args ns nd nexits ngoto nret rret res' n1 rargs,
     tr_exprlist c map nil (exprlist_of_expr_list (params_of_builtin_args args)) ns n1 rargs ->
     c!n1 = Some (Ibuiltin ef (convert_builtin_args args rargs) res' nd) ->
     tr_builtin_res map res res' ->
     tr_stmt c map (Sbuiltin res ef args) ns nd nexits ngoto nret rret
  | tr_Sseq: forall s1 s2 ns nd nexits ngoto nret rret n,
     tr_stmt c map s2 n nd nexits ngoto nret rret ->
     tr_stmt c map s1 ns n nexits ngoto nret rret ->
     tr_stmt c map (Sseq s1 s2) ns nd nexits ngoto nret rret
  | tr_Sifthenelse: forall a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse,
     tr_stmt c map strue ntrue nd nexits ngoto nret rret ->
     tr_stmt c map sfalse nfalse nd nexits ngoto nret rret ->
     tr_condition c map nil a ns ntrue nfalse ->
     tr_stmt c map (Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
  | tr_Sloop: forall sbody ns nd nexits ngoto nret rret nloop nend,
     tr_stmt c map sbody nloop nend nexits ngoto nret rret ->
     c!ns = Some(Inop nloop) ->
     c!nend = Some(Inop nloop) ->
     tr_stmt c map (Sloop sbody) ns nd nexits ngoto nret rret
  | tr_Sblock: forall sbody ns nd nexits ngoto nret rret,
     tr_stmt c map sbody ns nd (nd :: nexits) ngoto nret rret ->
     tr_stmt c map (Sblock sbody) ns nd nexits ngoto nret rret
  | tr_Sexit: forall n ns nd nexits ngoto nret rret,
     nth_error nexits n = Some ns ->
     tr_stmt c map (Sexit n) ns nd nexits ngoto nret rret
  | tr_Sswitch: forall a ns nd nexits ngoto nret rret,
     tr_exitexpr c map a ns nexits ->
     tr_stmt c map (Sswitch a) ns nd nexits ngoto nret rret
  | tr_Sreturn_none: forall nret nd nexits ngoto rret,
     tr_stmt c map (Sreturn None) nret nd nexits ngoto nret rret
  | tr_Sreturn_some: forall a ns nd nexits ngoto nret rret,
     tr_expr c map nil a ns nret rret None ->
     tr_stmt c map (Sreturn (Some a)) ns nd nexits ngoto nret (Some rret)
  | tr_Slabel: forall lbl s ns nd nexits ngoto nret rret n,
     ngoto!lbl = Some n ->
     c!n = Some (Inop ns) ->
     tr_stmt c map s ns nd nexits ngoto nret rret ->
     tr_stmt c map (Slabel lbl s) ns nd nexits ngoto nret rret
  | tr_Sgoto: forall lbl ns nd nexits ngoto nret rret,
     ngoto!lbl = Some ns ->
     tr_stmt c map (Sgoto lbl) ns nd nexits ngoto nret rret.

Inductive tr_function: CminorSel.function -> RTL.function -> Prop :=
  | tr_function_intro:
      forall f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret,
      add_vars init_mapping f.(CminorSel.fn_params) s0 = OK (rparams, map1) s1 i1 ->
      add_vars map1 f.(CminorSel.fn_vars) s1 = OK (rvars, map2) s2 i2 ->
      orret = ret_reg f.(CminorSel.fn_sig) rret ->
      tr_stmt code map2 f.(CminorSel.fn_body) nentry nret nil ngoto nret orret ->
      code!nret = Some(Ireturn orret) ->
      tr_function f (RTL.mkfunction
                       f.(CminorSel.fn_sig)
                       rparams
                       f.(CminorSel.fn_stackspace)
                       code
                       nentry).

Lemma tr_move_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall ns rs nd rd,
  tr_move s1.(st_code) ns rs nd rd ->
  tr_move s2.(st_code) ns rs nd rd.
Proof. induction 2; econstructor; eauto with rtlg. Qed.

Lemma tr_expr_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns nd rd dst,
  tr_expr s1.(st_code) map pr a ns nd rd dst ->
  tr_expr s2.(st_code) map pr a ns nd rd dst
with tr_condition_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns ntrue nfalse,
  tr_condition s1.(st_code) map pr a ns ntrue nfalse ->
  tr_condition s2.(st_code) map pr a ns ntrue nfalse
with tr_exprlist_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr al ns nd rl,
  tr_exprlist s1.(st_code) map pr al ns nd rl ->
  tr_exprlist s2.(st_code) map pr al ns nd rl.
Proof. intros s1 s2 EXT. pose (AT := fun pc i => instr_at_incr s1 s2 pc i EXT). induction 1; econstructor; eauto. eapply tr_move_incr; eauto. eapply tr_move_incr; eauto. intros s1 s2 EXT. pose (AT := fun pc i => instr_at_incr s1 s2 pc i EXT). induction 1; econstructor; eauto. intros s1 s2 EXT. pose (AT := fun pc i => instr_at_incr s1 s2 pc i EXT). induction 1; econstructor; eauto. Qed.

Lemma add_move_charact:
  forall s ns rs nd rd s' i,
  add_move rs rd nd s = OK ns s' i ->
  tr_move s'.(st_code) ns rs nd rd.
Proof. intros. unfold add_move in H. destruct (Reg.eq rs rd). inv H. constructor. constructor. eauto with rtlg. Qed.

Ltac custom_tac5 H0 := intros; inv H0.

Ltac custom_tac60  := econstructor; eauto.

Ltac custom_tac42  := right; eauto with rtlg.

Ltac custom_tac37 H0 := eapply H0; eauto.

Ltac custom_tac69 H0 := eauto with rtlg; eapply H0; eauto with rtlg.

Ltac custom_tac58  := econstructor; eauto with rtlg.

Ltac custom_tac26 H0 H1 := apply H0 with H1; auto.

Ltac custom_tac46  := constructor; auto.

Ltac custom_tac32 H0 := apply H0; eauto with rtlg.

Ltac custom_tac22 H0 := unfold H0; simpl.

Ltac custom_tac2 H0 := exists H0; auto.

Ltac custom_tac50 H0 H1 H2 := apply H0 with H1 H2; auto; eauto with rtlg.

Ltac custom_tac40  := eauto with rtlg; eauto with rtlg.

Ltac custom_tac51 H0 H1 H2 H3 H4 := generalize H0; unfold H1; caseEq ( nth_error ( map_letvars H2) H3); intros; inv H4.

Ltac custom_tac65 H0 := inv H0; constructor.

Ltac custom_tac41 H0 H1 := apply H0; apply H1.

Ltac custom_tac10  := red; intros.

Ltac custom_tac29 H0 H1 := eauto with rtlg; apply H0 with H1; eauto with rtlg.

Lemma transl_expr_charact:
  forall a map rd nd s ns s' pr INCR
     (TR: transl_expr map a rd nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: target_reg_ok map pr a rd)
     (VALID: regs_valid pr s)
     (VALID2: reg_valid rd s),
   tr_expr s'.(st_code) map pr a ns nd rd None

with transl_exprlist_charact:
  forall al map rl nd s ns s' pr INCR
     (TR: transl_exprlist map al rl nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: target_regs_ok map pr al rl)
     (VALID1: regs_valid pr s)
     (VALID2: regs_valid rl s),
   tr_exprlist s'.(st_code) map pr al ns nd rl

with transl_condexpr_charact:
  forall a map ntrue nfalse s ns s' pr INCR
     (TR: transl_condexpr map a ntrue nfalse s = OK ns s' INCR)
     (WF: map_valid map s)
     (VALID: regs_valid pr s),
   tr_condition s'.(st_code) map pr a ns ntrue nfalse. Proof. intro a. induction a; intros; try (monadInv TR); saturateTrans. generalize EQ; unfold find_var. caseEq (map_vars map)!i; intros; inv EQ1. econstructor; eauto. inv OK. left; split; congruence. right; eauto with rtlg. eapply add_move_charact; eauto. inv OK. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. inv OK. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. inv OK. econstructor. eauto with rtlg. apply tr_expr_incr with s1; auto. eapply transl_expr_charact; eauto 2 with rtlg. constructor; auto. apply tr_expr_incr with s0; auto. eapply transl_expr_charact; eauto 2 with rtlg. constructor; auto. inv OK. econstructor. eapply new_reg_not_in_map; eauto with rtlg. eapply transl_expr_charact; eauto 3 with rtlg. apply tr_expr_incr with s1; auto. eapply transl_expr_charact. eauto. apply add_letvar_valid; eauto with rtlg. constructor; auto. red; unfold reg_in_map. simpl. intros [[id A] | [B | C]]. elim H. left; exists id; auto. subst x. apply valid_fresh_absurd with rd s. auto. eauto with rtlg. elim H. right; auto. eauto with rtlg. eauto with rtlg. generalize EQ; unfold find_letvar. caseEq (nth_error (map_letvars map) n); intros; inv EQ0. monadInv EQ1. econstructor; eauto with rtlg. inv OK. left; split; congruence. right; eauto with rtlg. eapply add_move_charact; eauto. monadInv EQ1. inv OK. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. inv OK. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. induction al; intros; try (monadInv TR); saturateTrans. destruct rl; inv TR. constructor. destruct rl; simpl in TR; monadInv TR. inv OK. econstructor. eapply transl_expr_charact; eauto with rtlg. generalize (VALID2 r (in_eq _ _)). eauto with rtlg. apply tr_exprlist_incr with s0; auto. eapply transl_exprlist_charact; eauto with rtlg. apply regs_valid_cons. apply VALID2. auto with coqlib. auto. red; intros; apply VALID2; auto with coqlib. induction a; intros; try (monadInv TR); saturateTrans. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. econstructor; eauto with rtlg. apply tr_condition_incr with s1; eauto with rtlg. apply tr_condition_incr with s0; eauto with rtlg. econstructor; eauto with rtlg. eapply transl_expr_charact; eauto with rtlg. apply tr_condition_incr with s1; eauto with rtlg. eapply transl_condexpr_charact; eauto with rtlg. apply add_letvar_valid; eauto with rtlg. Qed.

Lemma transl_expr_assign_charact:
  forall id a map rd nd s ns s' INCR
     (TR: transl_expr map a rd nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: reg_map_ok map rd (Some id)),
   tr_expr s'.(st_code) map nil a ns nd rd (Some id).
Proof. intros id a. induction a; intros; monadInv TR; saturateTrans. generalize EQ; unfold find_var. caseEq (map_vars map)!i; intros; inv EQ1. econstructor; eauto. eapply add_move_charact; eauto. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. econstructor; eauto with rtlg. eapply transl_condexpr_charact; eauto with rtlg. apply tr_expr_incr with s1; auto. eapply IHa1; eauto 2 with rtlg. apply tr_expr_incr with s0; auto. eapply IHa2; eauto 2 with rtlg. econstructor. eapply new_reg_not_in_map; eauto with rtlg. eapply transl_expr_charact; eauto 3 with rtlg. apply tr_expr_incr with s1; auto. eapply IHa2; eauto. apply add_letvar_valid; eauto with rtlg. inv OK. constructor. auto. generalize EQ; unfold find_letvar. caseEq (nth_error (map_letvars map) n); intros; inv EQ0. monadInv EQ1. econstructor; eauto with rtlg. eapply add_move_charact; eauto. monadInv EQ1. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto with rtlg. Qed.

Lemma alloc_optreg_map_ok:
  forall map optid s1 r s2 i,
  map_valid map s1 ->
  alloc_optreg map optid s1 = OK r s2 i ->
  reg_map_ok map r optid.
Proof. unfold alloc_optreg; intros. destruct optid. constructor. unfold find_var in H0. destruct (map_vars map)!i0; monadInv H0. auto. constructor. eapply new_reg_not_in_map; eauto. Qed.

Lemma tr_exitexpr_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map a ns nexits,
  tr_exitexpr s1.(st_code) map a ns nexits ->
  tr_exitexpr s2.(st_code) map a ns nexits.
Proof. intros s1 s2 EXT. generalize tr_expr_incr tr_condition_incr; intros I1 I2. induction 1; econstructor; eauto with rtlg. Qed.

Lemma tr_stmt_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map s ns nd nexits ngoto nret rret,
  tr_stmt s1.(st_code) map s ns nd nexits ngoto nret rret ->
  tr_stmt s2.(st_code) map s ns nd nexits ngoto nret rret.
Proof. intros s1 s2 EXT. generalize tr_expr_incr tr_condition_incr tr_exprlist_incr tr_exitexpr_incr; intros I1 I2 I3 I4. pose (AT := fun pc i => instr_at_incr s1 s2 pc i EXT). induction 1; econstructor; eauto. Qed.

Lemma transl_exit_charact:
  forall nexits n s ne s' incr,
  transl_exit nexits n s = OK ne s' incr ->
  nth_error nexits n = Some ne /\ s' = s.
Proof. intros until incr. unfold transl_exit. destruct (nth_error nexits n); intro; monadInv H. auto. Qed.

Lemma transl_jumptable_charact:
  forall nexits tbl s nl s' incr,
  transl_jumptable nexits tbl s = OK nl s' incr ->
  tr_jumptable nexits tbl nl /\ s' = s.
Proof. intros nexits tbl. induction tbl; intros. monadInv H. split. red. simpl. intros. discriminate. auto. monadInv H. exploit transl_exit_charact; eauto. intros [A B]. exploit IHtbl; eauto. intros [C D]. split. red. simpl. intros. destruct (zeq v 0). inv H. exists x; auto. auto. congruence. Qed.

Lemma transl_exitexpr_charact:
  forall nexits a map s ns s' INCR
     (TR: transl_exitexpr map a nexits s = OK ns s' INCR)
     (WF: map_valid map s),
  tr_exitexpr s'.(st_code) map a ns nexits.
Proof. intros nexits a. induction a; simpl; intros; try (monadInv TR); saturateTrans. - exploit transl_exit_charact; eauto. intros [A B]. econstructor; eauto. - exploit transl_jumptable_charact; eauto. intros [A B]. econstructor; eauto. eapply transl_expr_charact; eauto with rtlg. eauto with rtlg. - econstructor. eapply transl_condexpr_charact; eauto with rtlg. apply tr_exitexpr_incr with s1; eauto with rtlg. apply tr_exitexpr_incr with s0; eauto with rtlg. - econstructor; eauto with rtlg. eapply transl_expr_charact; eauto with rtlg. apply tr_exitexpr_incr with s1; auto. eapply IHa; eauto with rtlg. apply add_letvar_valid; eauto with rtlg. Qed.

Lemma convert_builtin_res_charact:
  forall map oty res s res' s' INCR
    (TR: convert_builtin_res map oty res s = OK res' s' INCR)
    (WF: map_valid map s),
  tr_builtin_res map res res'.
Proof. intros map oty res. destruct res; simpl; intros. - monadInv TR. constructor. unfold find_var in EQ. destruct (map_vars map)!x; inv EQ; auto. - destruct (xtype_eq oty Xvoid); monadInv TR. + constructor. + constructor. eauto with rtlg. - monadInv TR. Qed.

Lemma transl_stmt_charact:
  forall map stmt nd nexits ngoto nret rret s ns s' INCR
    (TR: transl_stmt map stmt nd nexits ngoto nret rret s = OK ns s' INCR)
    (WF: map_valid map s)
    (OK: return_reg_ok s map rret),
  tr_stmt s'.(st_code) map stmt ns nd nexits ngoto nret rret.
Proof. intros map stmt. induction stmt; intros; simpl in TR; try (monadInv TR); saturateTrans. constructor. revert EQ. unfold find_var. case_eq (map_vars map)!i; intros; monadInv EQ. eapply tr_Sassign; eauto. eapply transl_expr_assign_charact; eauto with rtlg. constructor. auto. econstructor; eauto with rtlg. eapply transl_exprlist_charact; eauto 3 with rtlg. apply tr_expr_incr with s3; auto. eapply transl_expr_charact; eauto 4 with rtlg. destruct s0 as [b | id]; monadInv TR; saturateTrans. econstructor; eauto 4 with rtlg. eapply transl_expr_charact; eauto 3 with rtlg. apply tr_exprlist_incr with s5. auto. eapply transl_exprlist_charact; eauto 3 with rtlg. eapply alloc_regs_target_ok with (s1 := s0); eauto 3 with rtlg. apply regs_valid_cons; eauto 3 with rtlg. apply regs_valid_incr with s0; eauto 3 with rtlg. apply regs_valid_cons; eauto 3 with rtlg. apply regs_valid_incr with s2; eauto 3 with rtlg. eapply alloc_optreg_map_ok with (s1 := s2); eauto 3 with rtlg. econstructor; eauto 4 with rtlg. eapply transl_exprlist_charact; eauto 3 with rtlg. eapply alloc_optreg_map_ok with (s1 := s0); eauto 3 with rtlg. destruct s0 as [b | id]; monadInv TR; saturateTrans. assert (RV: regs_valid (x :: nil) s0). apply regs_valid_cons; eauto 3 with rtlg. econstructor; eauto 3 with rtlg. eapply transl_expr_charact; eauto 3 with rtlg. apply tr_exprlist_incr with s4; auto. eapply transl_exprlist_charact; eauto 4 with rtlg. econstructor; eauto 3 with rtlg. eapply transl_exprlist_charact; eauto 4 with rtlg. econstructor; eauto 4 with rtlg. eapply transl_exprlist_charact; eauto 3 with rtlg. eapply convert_builtin_res_charact; eauto with rtlg. econstructor. apply tr_stmt_incr with s0; auto. eapply IHstmt2; eauto with rtlg. eapply IHstmt1; eauto with rtlg. destruct (more_likely c stmt1 stmt2); monadInv TR. econstructor. apply tr_stmt_incr with s1; auto. eapply IHstmt1; eauto with rtlg. apply tr_stmt_incr with s0; auto. eapply IHstmt2; eauto with rtlg. eapply transl_condexpr_charact; eauto with rtlg. econstructor. apply tr_stmt_incr with s0; auto. eapply IHstmt1; eauto with rtlg. apply tr_stmt_incr with s1; auto. eapply IHstmt2; eauto with rtlg. eapply transl_condexpr_charact; eauto with rtlg. econstructor. apply tr_stmt_incr with s1; auto. eapply IHstmt; eauto with rtlg. eauto with rtlg. eauto with rtlg. econstructor. eapply IHstmt; eauto with rtlg. exploit transl_exit_charact; eauto. intros [A B]. econstructor. eauto. econstructor. eapply transl_exitexpr_charact; eauto. destruct o. destruct rret; inv TR. inv OK. econstructor; eauto with rtlg. eapply transl_expr_charact; eauto with rtlg. constructor. auto. simpl; tauto. monadInv TR. constructor. generalize EQ0; clear EQ0. case_eq (ngoto!l); intros; monadInv EQ0. generalize EQ1; clear EQ1. unfold handle_error. case_eq (update_instr n (Inop ns) s0); intros; inv EQ1. econstructor. eauto. eauto with rtlg. eapply tr_stmt_incr with s0; eauto with rtlg. generalize TR; clear TR. case_eq (ngoto!l); intros; monadInv TR. econstructor. auto. Qed.

Lemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof. intros until tf. unfold transl_function. caseEq (transl_fun f init_state). congruence. intros [nentry rparams] sfinal INCR TR E. inv E. monadInv TR. exploit add_vars_valid. eexact EQ1. apply init_mapping_valid. intros [A B]. exploit add_vars_valid. eexact EQ0. auto. intros [C D]. eapply tr_function_intro; eauto with rtlg. eapply transl_stmt_charact; eauto with rtlg. unfold ret_reg. destruct (xtype_eq (sig_res (CminorSel.fn_sig f)) Xvoid). constructor. constructor; eauto with rtlg. Qed.

