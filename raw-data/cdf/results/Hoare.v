Ltac custom0 H0 H16 H17 H18 H19 H20 H21 H22 H25 H26 H27 H28 H29 H30 H31 H32 H33 H36 H37 H38 H41 H42 H43 H44 H45 H46 H47 H48 H52 H56 H57 H58 H59 H60 H61 H62 H63 H66 H69 H70 H71 H72 H73 H74 H75 H76 H77 H82 H87 H88 H89 H90 H91 H92 H93 H94 H98 H102 H103 H104 H105 H106 H107 H108 H109 H112 H113 :=  intro H0; [induction H0; [intros H16 H17 H18 H19 H20 H21; [apply H22 in H20; [apply H22 in H21; [eapply H25; [apply H26 | Tauto | .. ] | .. ] | .. ] | .. ] | intros H27 H28 H29 H30 H31 H32; [apply H33 in H31; [apply H33 in H32; [eapply H36; [apply H37 | unfold H38 in *; [Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | intros H41 H42 H43 H44 H45 H46; [apply H47 in H45; [destruct H48 as ( R1 & C11 & C21 ); [apply H47 in H46; [destruct H52 as ( R2 & C12 & C22 )] | .. ] | .. ] | .. ] | intros H56 H57 H58 H59 H60 H61; [apply H62 in H60; [destruct H63 as ( C11 & C21 ); [apply H62 in H61; [destruct H66 as ( C12 & C22 ); [apply H69; [eapply H36; [eauto | Tauto | .. ] | eapply H36; [eauto | Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H70 H71 H72 H73 H74 H75; [apply H76 in H74; [destruct H77 as ( Inv1 & C1 & A1 & B1 ); [apply H76 in H75; [destruct H82 as ( Inv2 & C2 & A2 & B2 )] | .. ] | .. ] | .. ] | intros H87 H88 H89 H90 H91 H92; [apply H93 in H91; [destruct H94 as ( R1 & A1 & B1 ); [apply H93 in H92; [destruct H98 as ( R2 & A2 & B2 ); [eapply H102; [ | Tauto | Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H103 H104 H105 H106 H107 H108; [apply H109 in H107; [apply H109 in H108; [eapply H36; [apply H112 | unfold H38, H113 in *; [Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom1 H0 H1 H2 H3 H4 :=  apply H0; [unfold H1; [congruence | .. ] | cbn | intros H2 H3 H4; [inv H4 | .. ] | .. ].
Ltac custom2 H0 H16 H17 H18 H22 H23 H24 H25 H26 H2 H1 H28 H29 H30 H31 H32 H33 H19 H6 H5 H47 H34 H20 H36 H37 H35 H48 H40 H41 H39 H4 H42 H38 H3 H43 H44 H45 H46 :=  induction H0; [intros H16 H17 H18; [assert ( H' : forall x, H16 x -->> H17 x ) by ( intros ; apply Hoare_skip_inv ; auto ); [eapply H22; [apply H23 | .. ] | .. ] | .. ] | intros H24 H25 H26; [assert ( H' : forall y, H24 y -->> aupdate H2 H1 ( H25 y ) ); [intros H28; [apply H29; [auto | .. ] | .. ] | eapply H22; [apply H30 | .. ] | .. ] | .. ] | intros H31 H32 H33; [set ( REL := fun ( x : H19 ) ( R : assertion ) => Hoare ( H31 x ) H6 R /\ Hoare R H5 ( H32 x ) ); [assert ( H' : exists R : H19 -> assertion, forall x : H47, H34 x ( R x ) ); [apply H20; [intros H36; [apply H37; [auto | .. ] | .. ] | .. ] | destruct H35 as ( R & H48 ); [apply H40 with ( H41 H39 ); [apply H4; [intros H42; [apply H38 | .. ] | .. ] | apply H3; [intros H43; [apply H38 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H44 H45 H46 | .. ].
Ltac custom3 H0 H20 H21 H22 H1 H2 H23 H24 H25 H3 H4 H26 H5 H6 H27 H28 H29 H7 H8 H9 H79 H10 H11 H30 H12 H13 H80 H14 H15 H16 H17 H31 H18 H19 H32 H33 H34 H35 H47 H48 H49 H45 H91 H51 H52 H53 H46 H55 H56 H57 H92 H50 H59 H44 H93 H58 H63 H64 H65 H94 H60 H67 H68 H69 H62 H66 H95 H72 H71 H73 H74 H75 H76 H77 H43 H78 H70 :=  custom2 H0 H20 H21 H22 H1 H2 H23 H24 H25 H3 H4 H26 H5 H6 H27 H28 H29 H7 H8 H9 H79 H10 H11 H30 H12 H13 H80 H14 H15 H16 H17 H31 H18 H19 H32 H33 H34 H35; [ |  |  | intros H55 H56 H57; [set ( REL := fun ( x : H7 ) ( Inv : assertion ) => Hoare ( atrue H44 //\\ Inv ) H0 Inv /\ ( H55 x -->> Inv ) /\ ( afalse H93 //\\ Inv -->> H56 x ) ); [assert ( H' : exists Inv : H7 -> assertion, forall x : H94, H60 x ( Inv x ) ); [apply H11; [intros H74; [apply H76; [auto | .. ] | .. ] | .. ] | destruct H66 as ( Inv & H95 ); [eapply H63 with ( H55 := H72 H71 ); [apply H75; [apply H1 with ( H55 := H72 ( fun x => H77 H44 //\\ H71 x ) ); [apply H43; [intros H78; [apply H70 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H47 H48 H49; [set ( REL := fun ( x : H7 ) ( R : assertion ) => ( H47 x -->> atrue H45 //\\ R ) /\ ( atrue H91 //\\ R -->> H48 x ) ); [assert ( H' : exists R : H7 -> assertion, forall x : H92, H50 x ( R x ) ); [apply H11; [intros H67; [apply H73; [auto | .. ] | .. ] | .. ] | destruct H58 as ( R & A ); [eapply H63; [apply H68 with ( H47 := H69 H62 ) | .. ] | .. ] | .. ] | .. ] | .. ] | intros H51 H52 H53; [assert ( H' : forall y, H51 y -->> aforall ( fun n => aupdate H46 ( CONST n ) ( H52 y ) ) ); [intros H59; [apply H65; [auto | .. ] | .. ] | eapply H1; [apply H64 | .. ] | .. ] | .. ] | .. ].
Ltac custom4  :=  split; [auto | auto | .. ].
Ltac custom5 H0 :=  apply H0; [auto | .. ].
Ltac custom6 H0 H1 H4 H5 :=  apply H0; [eapply H1; [eauto | cbn; [intros H4 H5; [tauto | .. ] | .. ] | .. ] | .. ].
Ltac custom7  :=  red; [auto | .. ].
Ltac custom8 H0 H1 H2 H4 H3 :=  apply H0; [intros H1; [specialize ( H2 H1 ); [apply H4 in H3; [tauto] | .. ] | .. ] | .. ].
Ltac custom9 H0 H1 H2 H3 H4 H5 H6 H9 H7 H8 :=  eapply H0; [apply H1 | intros H2 [ H3 H4 ]; [replace H5 with ( if beval H6 H2 then H9 else H7 ); [eapply H8; [eexact H4 | constructor | .. ] | rewrite H3; [auto | .. ] | .. ] | .. ] | .. ].
Ltac custom10 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 :=  intros H0 H1 H2 H3 H4 H5 H6; [intros H7 H8; [custom1 H9 H10 H11 H12 H13; [auto | destruct ( beval H2 H12 ) eqn : B; [apply H5; [custom4  | .. ] | apply H6; [custom4  | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom11 H0 :=  eapply H0; [eauto | .. ].
Ltac custom12 H0 H1 :=  apply H0 with H1; [auto | auto | .. ].
Ltac custom13 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H14 :=  intros H0 H1; [intros H2 [ H3 H4 ]; [custom1 H5 H6 H7 H8 H9; [red in H3; [congruence] | apply H14; [custom7  | custom4  | .. ] | .. ] | .. ] | .. ].
Ltac custom14 H0 H1 H2 H3 H4 H7 :=  simpl in H0; [apply H1 with H2; [intros H3 H4; [rewrite H7; [auto | auto | .. ] | .. ] | auto | .. ] | .. ].
Ltac custom15 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1; [intros H2 H3; [custom1 H4 H5 H6 H7 H8; [auto | constructor; [custom7  | apply H3 | .. ] | .. ] | .. ] | .. ].
Ltac custom16 H0 :=  exists H0; [split | .. ].
Ltac custom17 H0 H1 H8 H2 H9 H5 :=  apply H0 with ( H1 := H8 ) ( H2 := H9 ); [auto | unfold H5; [auto | .. ] | unfold H5; [auto | .. ] | .. ].
Ltac custom18 H0 H1 H2 H3 H4 :=  apply H0; [unfold H1; [congruence | .. ] | cbn; [auto | .. ] | intros H2 H3 H4 | .. ].
Ltac custom19 H0 H1 H2 :=  intros H0; [eapply H1; [apply H2 | .. ] | .. ].
Ltac custom20 H0 H1 :=  intros H0 H1; [simpl; [auto | .. ] | .. ].
Ltac custom21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 :=  intros H0 H1 H2 H3 H4; [custom1 H5 H6 H7 H8 H9; [tauto | apply H10; [reflexivity | exact H4 | .. ] | .. ] | .. ].
Ltac custom22 H0 :=  custom5 H0; [auto | .. ].
Ltac custom23 H0 H1 :=  eapply H0; [eexact H1 | .. ].
Ltac custom24 H0 :=  custom16 H0; [auto | split; [Tauto | Tauto | .. ] | .. ].
Ltac custom25 H0 H1 H2 H3 :=  intros H0 ( H1 & H2 ); [exists H1; [custom5 H3 | .. ] | .. ].
Ltac custom26 H0 H1 H2 :=  apply H0; [eapply H1; [custom11 H2; [eauto | .. ] | Tauto | .. ] | .. ].
Ltac custom27 H0 :=  intros H0; [simpl in H0 | .. ].
Ltac custom28 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [inv H4 | .. ].
Ltac custom29 H0 H1 H2 H3 :=  custom11 H0; [intros H1 [ H2 H3 ]; [custom4  | .. ] | eauto | .. ].
Ltac custom30 H0 H1 H2 H3 H4 :=  custom11 H0; [intros H1 ( H2 & H3 & H4 ); [exists H3; [custom4  | .. ] | .. ] | .. ].
Ltac custom31  :=  split; [auto | .. ].
Ltac custom32 H0 H1 H7 H2 H3 H4 H5 H6 :=  eapply H0 with ( H1 := H7 //\\ H2 ); [custom6 H3 H4 H5 H6 | Tauto | Tauto | .. ].
Ltac custom33 H0 H6 H7 :=  dependent induction H0; [custom7  | red; [intros H6 H7 | .. ] | .. ].
Ltac custom34 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3; [reflexivity | auto | .. ] | .. ].
Ltac custom35 H0 H1 H9 :=  intros H0 H1; [destruct H0; [constructor | custom22 H9 | .. ] | .. ].
Ltac custom36 H0 H1 :=  custom23 H0 H1; [constructor | .. ].
Ltac custom37 H0 H1 :=  exists H0; [apply H1; [custom4  | .. ] | .. ].
Ltac custom38 H0 :=  custom11 H0; [eauto | .. ].
Ltac custom39 H0 H1 H2 H3 H4 :=  custom11 H0; [intros H1 ( H2 & H3 ) H4; [custom4  | .. ] | .. ].
Ltac custom40 H0 H1 :=  custom11 H0; [unfold H1; [congruence | .. ] | .. ].
Ltac custom41 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 :=  intros H0 H1 H2 H3 H4 H5 H6; [intros H7 H8; [custom12 H9 H1 | .. ] | .. ].
Ltac custom42 H0 :=  custom16 H0; [Tauto | Tauto | .. ].
Ltac custom43 H0 H1 H2 :=  custom16 H0; [custom12 H1 H2 | auto | .. ].
Ltac custom44 H0 H2 H3 H5 H4 :=  custom27 H0; [eapply H2 with ( H3 := H5 //\\ H4 ); [ |  | Tauto | .. ] | .. ].
Ltac custom45 H0 H1 H2 H3 H4 H5 H6 H7 H9 H10 :=  intros H0 H1 H2 H3 H4 H5 H6 H7; [assert ( REC : forall H4 s, safe H1 H9 s -> safe H3 H10 s ); [ | custom7  | .. ] | .. ].
Ltac custom46 H0 H1 :=  split; [ | unfold H0, H1; [auto | .. ] | .. ].
Ltac custom47 H0 H1 H2 :=  apply H0, H1, H2; [auto | auto | .. ].
Ltac custom48 H0 H1 :=  apply H0 in H1; [assumption | custom7  | .. ].
Ltac custom49 H0 H1 H2 H3 H4 :=  eapply H0; [apply H1 | intros H2 [ H3 H4 ] | .. ].
Ltac custom50 H0 :=  eapply H0; [ | Tauto | Tauto | .. ].
Ltac custom51 H0 H1 H2 :=  custom23 H0 H1; [apply H2 | .. ].
Ltac custom52 H0 :=  exists H0; [auto | .. ].
Ltac custom53 H0 H1 :=  apply H0 with H1; [auto | .. ].
Ltac custom54 H2 H0 H1 H3 H4 :=  custom19 H2 H0 H1; [intros H3 H4 | .. ].
Ltac custom55 H0 H1 :=  intros H0; [apply H1 | .. ].
Ltac custom56 H0 H1 H2 H3 H4 H5 :=  custom28 H0 H1 H2 H3 H4; [custom16 H5 | .. ].
Ltac custom57 H0 H1 H2 :=  intros H0 [ H1 H2 ]; [custom4  | .. ].
Ltac custom58 H0 H1 H2 H3 :=  intros H0 H1 H2; [custom5 H3 | .. ].
Ltac custom59 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3 | .. ].
Ltac custom60 H0 :=  custom22 H0; [auto | .. ].
Ltac custom61 H0 H1 :=  destruct ( beval H0 H1 ); [auto | .. ].
Ltac custom62 H0 :=  rewrite H0; [auto | .. ].
Ltac custom63 H0 H1 H2 H3 H4 :=  custom1 H0 H1 H2 H3 H4; [auto | .. ].
Ltac custom64 H0 H1 :=  custom36 H0 H1; [auto | .. ].
Ltac custom65  :=  custom31 ; [congruence | .. ].
Ltac custom66 H0 :=  apply H0; [custom4  | .. ].
Ltac custom67 H0 H1 H8 :=  destruct ( H0 H1 ) as ( B & C ); [custom5 H8].
Ltac custom68 H0 H1 H2 H3 :=  apply H0 with ( H1 H2 H3 ); [ | auto | .. ].
Ltac custom69 H0 :=  split; [ | exact H0 | .. ].
Ltac custom70 H0 H1 :=  eapply H0; [apply H1 | .. ].
Ltac custom71 H0 :=  eapply H0; [ | custom7  | .. ].
Ltac custom72 H0 H1 H2 H3 :=  intros H0 H1 H2 H3; [dependent induction H3 | .. ].
Ltac custom73 H0 H1 :=  intros H0 H1; [simpl | .. ].
Ltac custom74 H0 H1 H2 :=  intros H0 H1; [custom5 H2 | .. ].
Ltac custom75 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [dependent induction H4 | .. ].

Lemma update_same : forall x v s, ( update x v s ) x = v .
Proof.
   unfold update. intros x v s. destruct ( string_dec x x ) as [  e | n ].
    - congruence.
    - congruence.
Qed.

Lemma update_other : forall x v s y, x <> y -> ( update x v s ) y = s y .
Proof.
   unfold update. intros x v s y H. destruct ( string_dec x y ) as [  e | n ].
    - congruence.
    - congruence.
Qed.

(** The relation [ red (c, s) (c', s') ], written [ c / s --> c' / s' ]
    in the lectures, defines a basic reduction, that is, the first
    computation step when executing command [c] in initial memory
    state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b s then c1 else c2), s)
  | red_while_done: forall b c s,
      beval b s = false ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval b s = true ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s)
  | red_havoc: forall x s n,
      red (HAVOC x, s) (SKIP, update x n s)
  | red_assert: forall b s,
      beval b s = true ->
      red (ASSERT b, s) (SKIP, s).


(** The predicate [ error c s ] means that command [c] started in state [s]
    causes a run-time error.
    This is written [ c / s --> err ] in the lectures. *)

Fixpoint error (c: com) (s: store) : Prop :=
  match c with
  | ASSERT b => beval b s = false
  | (c1 ;; c2) => error c1 s
  | _ => False
  end.

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c: com) (s s': store) : Prop :=
  exists c', star red (c, s) (c', s') /\ terminated c'.

Definition goeswrong (c: com) (s: store) : Prop :=
  exists c' s', star red (c, s) (c', s') /\ error c' s'.



(** * 2.  Hoare logic *)

(** ** 2.1.  Assertions on the values of variables *)

(** Hoare logic manipulates formulas / claims / assertions that "talk about"
    the values of the program variables.  A typical assertion is
    [0 <= x /\ x <= y], meaning "at this program point, the value of
    variable [x] is positive and less than or equal to the value of
    variable [y]". *)

(** In our Coq development, we represent assertions by Coq logical formulas
    (type [Prop]) parameterized by the current store, which provides
    the values of the variables.

    For example, the assertion [0 <= x /\ x <= y] above is represented
    by the Coq predicate [fun s => 0 <= s "x" /\ s "x" <= s "y"]. *)


(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)


(** Quantification. *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

(** ** 2.2.  The rules of Hoare logic *)

(** Here are the base rules for weak Hoare logic.
    They define a relation [ ⦃P⦄ c ⦃Q⦄], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Reserved Notation "⦃ P ⦄ c ⦃ Q ⦄" (at level 90, c at next level).

Inductive Hoare: assertion -> com -> assertion -> Prop :=
  | Hoare_skip: forall P,
      ⦃ P ⦄ SKIP ⦃ P ⦄
  | Hoare_assign: forall P x a,
      ⦃ aupdate x a P ⦄ ASSIGN x a ⦃ P ⦄
  | Hoare_seq: forall P Q R c1 c2,
      ⦃ P ⦄ c1 ⦃ Q ⦄ ->
      ⦃ Q ⦄ c2 ⦃ R ⦄ ->
      ⦃ P ⦄ c1;;c2 ⦃ R ⦄
  | Hoare_ifthenelse: forall P Q b c1 c2,
      ⦃ atrue b //\\ P ⦄ c1 ⦃ Q ⦄ ->
      ⦃ afalse b //\\ P ⦄ c2 ⦃ Q ⦄ ->
      ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄
  | Hoare_while: forall P b c,
      ⦃ atrue b //\\ P ⦄ c ⦃ P ⦄ ->
      ⦃ P ⦄ WHILE b c ⦃ afalse b //\\ P ⦄
  | Hoare_havoc: forall x Q,
      ⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄ HAVOC x ⦃ Q ⦄
  | Hoare_assert: forall P b,
      ⦃ atrue b //\\ P ⦄ ASSERT b ⦃ atrue b //\\ P ⦄
  | Hoare_consequence: forall P Q P' Q' c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦃ P' ⦄ c ⦃ Q' ⦄

where "⦃ P ⦄ c ⦃ Q ⦄" := (Hoare P c Q).

(** Here are the rules for strong Hoare logic, defining strong triples
    [ 〚P〛 c 〚Q〛 ] that guarantee that [c] terminates.
    The only difference with weak triples is the rule for [while] loops. *)

Reserved Notation "〚 P 〛 c 〚 Q 〛" (at level 90, c at next level).

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun s => 0 <= aeval a s < v.

Inductive HOARE: assertion -> com -> assertion -> Prop :=
  | HOARE_skip: forall P,
      〚 P 〛 SKIP 〚 P 〛
  | HOARE_assign: forall P x a,
      〚 aupdate x a P 〛 ASSIGN x a 〚 P 〛
  | HOARE_seq: forall P Q R c1 c2,
      〚 P 〛 c1 〚 Q 〛 ->
      〚 Q 〛 c2 〚 R 〛 ->
      〚 P 〛 c1;;c2 〚 R 〛
  | HOARE_ifthenelse: forall P Q b c1 c2,
      〚 atrue b //\\ P 〛 c1 〚 Q 〛 ->
      〚 afalse b //\\ P 〛 c2 〚 Q 〛 ->
      〚 P 〛 IFTHENELSE b c1 c2 〚 Q 〛
  | HOARE_while: forall P b c a,
      (forall v,
         〚 atrue b //\\ aequal a v //\\ P 〛 c 〚 alessthan a v //\\ P 〛) ->
      〚 P 〛 WHILE b c 〚 afalse b //\\ P 〛
  | HOARE_havoc: forall x Q,
      〚 aforall (fun n => aupdate x (CONST n) Q) 〛 HAVOC x 〚 Q 〛
  | HOARE_assert: forall P b,
      〚 atrue b //\\ P 〛 ASSERT b 〚 atrue b //\\ P 〛
  | HOARE_consequence: forall P Q P' Q' c,
      〚 P 〛 c 〚 Q 〛 ->
      P' -->> P ->
      Q -->> Q' ->
      〚 P' 〛 c 〚 Q' 〛

where "〚 P 〛 c 〚 Q 〛" := (HOARE P c Q).

(** ** 2.3. Derived and admissible rules *)

Ltac custom17 H0 H1 H8 H2 H9 H5 :=  apply H0 with ( H1 := H8 ) ( H2 := H9 ); [auto | unfold H5; [auto | .. ] | unfold H5; [auto | .. ] | .. ].
Lemma Hoare_consequence_pre : forall P P' Q c, ⦃ P ⦄ c ⦃ Q ⦄ -> P' -->> P -> ⦃ P' ⦄ c ⦃ Q ⦄ .
Proof.
   intros P P' Q c H H0. custom17 Hoare_consequence P P Q Q aimp.
Qed.

Lemma Hoare_consequence_post : forall P Q Q' c, ⦃ P ⦄ c ⦃ Q ⦄ -> Q -->> Q' -> ⦃ P ⦄ c ⦃ Q' ⦄ .
Proof.
   intros P Q Q' c H H0. custom17 Hoare_consequence P P Q Q aimp.
Qed.

Ltac custom31  :=  split; [auto | .. ].
Ltac custom16 H0 :=  exists H0; [split | .. ].
Ltac custom7  :=  red; [auto | .. ].
Ltac custom70 H0 H1 :=  eapply H0; [apply H1 | .. ].
Lemma Floyd_assign : forall P x a, ⦃ P ⦄ ASSIGN x a ⦃ aexists ( fun x0 => aexists ( fun v => aequal ( VAR x ) v //\\ aupdate x ( CONST x0 ) ( P //\\ aequal a v ) ) ) ⦄ .
Proof.
   intros P x a. custom70 Hoare_consequence_pre Hoare_assign. intros s Ps. set ( x0 := s x ). set ( v := aeval a s ). set ( s' := update x v s ). set ( s'' := update x x0 s' ). assert ( s'' = s ).
    - apply functional_extensionality. intros x1. unfold s'', s', update. destruct ( string_dec x x1 ) as [  e | n ].
      -- subst x1. auto.
      -- auto.
    - unfold aupdate. exists x0. custom16 v.
      -- red. cbn. apply update_same.
      -- cbn. fold v. fold s'. fold s''. rewrite H. custom31. custom7.
Qed.

(** Some derived constructs, with proof rules. *)

Ltac custom5 H0 :=  apply H0; [auto | .. ].
Lemma Hoare_ifthen : forall b c P Q, ⦃ atrue b //\\ P ⦄ c ⦃ Q ⦄ -> afalse b //\\ P -->> Q -> ⦃ P ⦄ IFTHENELSE b c SKIP ⦃ Q ⦄ .
Proof.
   intros b c P Q H H0. custom5 Hoare_ifthenelse. apply Hoare_consequence_pre with Q.
    - auto using Hoare_skip.
    - auto using Hoare_skip.
Qed.

Definition DOWHILE (c: com) (b: bexp) : com :=
  c ;; WHILE b c.

Ltac custom53 H0 H1 :=  apply H0 with H1; [auto | .. ].
Ltac custom12 H0 H1 :=  apply H0 with H1; [auto | auto | .. ].
Lemma Hoare_dowhile : forall P b c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> ( atrue b //\\ Q -->> P ) -> ⦃ P ⦄ DOWHILE c b ⦃ afalse b //\\ Q ⦄ .
Proof.
   intros P b c Q H H0. custom53 Hoare_seq Q. apply Hoare_while. custom12 Hoare_consequence_pre P.
Qed.

(** A frame rule for strong triples.  Used to reason about "for" loops below. *)

Fixpoint assigns (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | SEQ c1 c2 => assigns c1 x \/ assigns c2 x
  | IFTHENELSE b c1 c2 => assigns c1 x \/ assigns c2 x
  | WHILE b c => assigns c x
  | ASSERT b => False
  | HAVOC y => x = y
  end.

Definition independent (A: assertion) (vars: ident -> Prop) : Prop :=
  forall (s1 s2: store),
  (forall x, ~ vars x -> s1 x = s2 x) ->
  A s1 -> A s2.


Ltac custom4  :=  split; [auto | auto | .. ].
Ltac custom14 H0 H1 H2 H3 H4 H7 :=  simpl in H0; [apply H1 with H2; [intros H3 H4; [rewrite H7; [auto | auto | .. ] | .. ] | auto | .. ] | .. ].
Ltac custom27 H0 :=  intros H0; [simpl in H0 | .. ].
Ltac custom6 H0 H1 H4 H5 :=  apply H0; [eapply H1; [eauto | cbn; [intros H4 H5; [tauto | .. ] | .. ] | .. ] | .. ].
Ltac custom32 H0 H1 H7 H2 H3 H4 H5 H6 :=  eapply H0 with ( H1 := H7 //\\ H2 ); [custom6 H3 H4 H5 H6 | Tauto | Tauto | .. ].
Ltac custom44 H0 H2 H3 H5 H4 :=  custom27 H0; [eapply H2 with ( H3 := H5 //\\ H4 ); [ |  | Tauto | .. ] | .. ].
Ltac custom50 H0 :=  eapply H0; [ | Tauto | Tauto | .. ].
Ltac custom57 H0 H1 H2 :=  intros H0 [ H1 H2 ]; [custom4  | .. ].
Ltac custom62 H0 :=  rewrite H0; [auto | .. ].
Lemma HOARE_frame:
  forall R P c Q,
  〚 P 〛 c 〚 Q 〛 ->
  independent R (assigns c) ->
  〚 P //\\ R 〛 c 〚 Q //\\ R 〛.
  Proof.
  intros R. assert ( IND_SUB : forall ( vars1 vars2 : ident -> Prop ), independent R vars1 -> ( forall x, vars2 x -> vars1 x ) -> independent R vars2 ).
   - unfold independent. intros vars1 vars2 H H0 s1 s2 H1 H2. custom12 H s1.
   - induction 1.
     -- custom27 IND. apply HOARE_skip.
     -- intros IND. eapply HOARE_consequence with ( Q := P //\\ R ).
       --- apply HOARE_assign.
       --- unfold aupdate. intros s [ A B ]. custom31. custom14 IND IND s y DIFF update_other.
       --- Tauto.
     -- custom27 IND. apply HOARE_seq with ( Q //\\ R ).
       --- custom6 IHHOARE1 IND_SUB x H1.
       --- custom6 IHHOARE2 IND_SUB x H1.
     -- custom27 IND. apply HOARE_ifthenelse.
       --- custom32 HOARE_consequence Q Q R IHHOARE1 IND_SUB x H1.
       --- custom32 HOARE_consequence Q Q R IHHOARE2 IND_SUB x H1.
     -- intros IND. eapply HOARE_consequence with (P := P //\\ R).
      apply HOARE_while with a. intros.
      eapply HOARE_consequence. apply ( H0 v ). auto.
      Tauto. Tauto. Tauto. Tauto.
     -- custom44 IND HOARE_consequence Q Q R.
       --- apply HOARE_havoc.
       --- intros s [ A B ] n. split.
         ---- apply A.
         ---- apply IND with s.
           ----- intros y DIFF. custom62 update_other. auto.
           ----- auto.
     -- custom27 IND. eapply HOARE_consequence. apply HOARE_assert with ( P := P //\\ R ).
        Tauto. Tauto.
     -- custom27 IND. eapply HOARE_consequence.
       --- custom5 IHHOARE.
       --- custom57 s A B.
       --- custom57 s A B.
Qed.

(** A counted "for" loop. *)

Definition FOR (i: ident) (l: aexp) (h: ident) (c: com) : com :=
  ASSIGN i l;;
  WHILE (LESSEQUAL (VAR i) (VAR h)) (c ;; ASSIGN i (PLUS (VAR i) (CONST 1))).

Ltac custom69 H0 :=  split; [ | exact H0 | .. ].
Lemma HOARE_for : forall l h i c P, 〚 atrue ( LESSEQUAL ( VAR i ) ( VAR h ) ) //\\ P 〛 c 〚 aupdate i ( PLUS ( VAR i ) ( CONST 1 ) ) P 〛 -> ~ assigns c i -> ~ assigns c h -> i <> h -> 〚 aupdate i l P 〛 FOR i l h c 〚 afalse ( LESSEQUAL ( VAR i ) ( VAR h ) ) //\\ P 〛 .
Proof.
   intros l h i c P H H0 H1 H2. apply HOARE_seq with P.
    - apply HOARE_assign.
    - set ( variant := PLUS ( MINUS ( VAR h ) ( VAR i ) ) ( CONST 1 ) ). apply HOARE_while with ( a := variant ). intro v. eapply HOARE_seq.
      -- eapply HOARE_consequence.
        --- apply HOARE_frame with ( R := aequal variant v //\\ atrue ( LESSEQUAL ( VAR i ) ( VAR h ) ) ).
          ---- eexact H.
          ---- intros s1 s2 E. unfold aequal, atrue, aand. simpl. rewrite ( E i ), ( E h ) by auto. auto.
        --- Tauto.
        --- intros s A. eexact A.
      -- eapply HOARE_consequence with ( Q := alessthan variant v //\\ P ).
        --- apply HOARE_assign.
        --- intros s ( A & B & C ). unfold aequal in B. simpl in B. unfold atrue in C. simpl in C. apply Z.leb_le in C. custom69 A. red. simpl. rewrite update_same. rewrite update_other by auto. lia.
        --- Tauto.
Qed.

(** Some inversion lemmas. *)

Ltac custom33 H0 H6 H7 :=  dependent induction H0; [custom7  | red; [intros H6 H7 | .. ] | .. ].
Ltac custom47 H0 H1 H2 :=  apply H0, H1, H2; [auto | auto | .. ].
Lemma Hoare_skip_inv : forall P Q, ⦃ P ⦄ SKIP ⦃ Q ⦄ -> ( P -->> Q ) .
Proof.
   intros P Q H. custom33 H s H2. custom47 H1 IHHoare H0.
Qed.

Lemma Hoare_assign_inv : forall x a P Q, ⦃ P ⦄ ASSIGN x a ⦃ Q ⦄ -> ( P -->> aupdate x a Q ) .
Proof.
   intros x a P Q H. custom33 H s H2. red. custom47 H1 IHHoare H0.
Qed.

Lemma Hoare_seq_inv: forall c1 c2 P Q,
  ⦃ P ⦄ c1 ;; c2  ⦃ Q  ⦄ ->
  exists R, ⦃ P ⦄ c1 ⦃ R ⦄ /\ ⦃ R ⦄ c2 ⦃ Q ⦄.
Proof.
  intros c1 c2 P Q H; dependent induction H.
- exists Q; auto.
- edestruct IHHoare as (R & C1 & C2); eauto.
  exists R; split; eauto using Hoare_consequence_pre, Hoare_consequence_post.
Qed.

Lemma Hoare_ifthenelse_inv: forall b c1 c2 P Q,
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ ->
  ⦃ atrue b //\\ P ⦄ c1 ⦃ Q ⦄ /\ ⦃ afalse b //\\ P ⦄ c2 ⦃ Q ⦄.
Proof.
  intros b c1 c2 P Q H; dependent induction H.
- split; auto.
- edestruct IHHoare as (C1 & C2); eauto.
  split; eapply Hoare_consequence; eauto.
  intros s [A B]; split; auto.
  intros s [A B]; split; auto.
Qed.

Ltac custom75 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [dependent induction H4 | .. ].
Ltac custom24 H0 :=  custom16 H0; [auto | split; [Tauto | Tauto | .. ] | .. ].
Lemma Hoare_while_inv : forall b c P Q, ⦃ P ⦄ WHILE b c ⦃ Q ⦄ -> exists Inv, ⦃ atrue b //\\ Inv ⦄ c ⦃ Inv ⦄ /\ ( P -->> Inv ) /\ ( afalse b //\\ Inv -->> Q ) .
Proof.
   custom75 b c P Q H.
    - custom24 P.
    - edestruct IHHoare as ( Inv & C & X & Y ).
      -- eauto.
      -- custom24 Inv.
Qed.

Ltac custom72 H0 H1 H2 H3 :=  intros H0 H1 H2 H3; [dependent induction H3 | .. ].
Ltac custom22 H0 :=  custom5 H0; [auto | .. ].
Ltac custom59 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3 | .. ].
Lemma Hoare_havoc_inv : forall x P Q, ⦃ P ⦄ HAVOC x ⦃ Q ⦄ -> ( P -->> aforall ( fun n => aupdate x ( CONST n ) Q ) ) .
Proof.
   custom72 x P Q H.
    - custom7.
    - custom59 s Ps n H1. custom22 IHHoare.
Qed.

Ltac custom42 H0 :=  custom16 H0; [Tauto | Tauto | .. ].
Lemma Hoare_assert_inv : forall b P Q, ⦃ P ⦄ ASSERT b ⦃ Q ⦄ -> exists R, ( P -->> atrue b //\\ R ) /\ ( atrue b //\\ R -->> Q ) .
Proof.
   custom72 b P Q H.
    - custom42 P.
    - edestruct IHHoare as ( R & A & B ).
      -- eauto.
      -- custom42 R.
Qed.

(** Some admissible rules. *)

Ltac custom11 H0 :=  eapply H0; [eauto | .. ].
Ltac custom26 H0 H1 H2 :=  apply H0; [eapply H1; [custom11 H2; [eauto | .. ] | Tauto | .. ] | .. ].
Ltac custom0 H0 H16 H17 H18 H19 H20 H21 H22 H25 H26 H27 H28 H29 H30 H31 H32 H33 H36 H37 H38 H41 H42 H43 H44 H45 H46 H47 H48 H52 H56 H57 H58 H59 H60 H61 H62 H63 H66 H69 H70 H71 H72 H73 H74 H75 H76 H77 H82 H87 H88 H89 H90 H91 H92 H93 H94 H98 H102 H103 H104 H105 H106 H107 H108 H109 H112 :=  intro H0; [induction H0; [intros H16 H17 H18 H19 H20 H21; [apply H22 in H20; [apply H22 in H21; [eapply H25; [apply H26 | Tauto | .. ] | .. ] | .. ] | .. ] | intros H27 H28 H29 H30 H31 H32; [apply H33 in H31; [apply H33 in H32; [eapply H36; [apply H37 | unfold H38 in *; [Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | intros H41 H42 H43 H44 H45 H46; [apply H47 in H45; [destruct H48 as ( R1 & C11 & C21 ); [apply H47 in H46; [destruct H52 as ( R2 & C12 & C22 )] | .. ] | .. ] | .. ] | intros H56 H57 H58 H59 H60 H61; [apply H62 in H60; [destruct H63 as ( C11 & C21 ); [apply H62 in H61; [destruct H66 as ( C12 & C22 ); [apply H69; [eapply H36; [eauto | Tauto | .. ] | eapply H36; [eauto | Tauto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H70 H71 H72 H73 H74 H75; [apply H76 in H74; [destruct H77 as ( Inv1 & C1 & A1 & B1 ); [apply H76 in H75; [destruct H82 as ( Inv2 & C2 & A2 & B2 )] | .. ] | .. ] | .. ] | intros H87 H88 H89 H90 H91 H92; [apply H93 in H91; [destruct H94 as ( R1 & A1 & B1 ); [apply H93 in H92; [destruct H98 as ( R2 & A2 & B2 ); [eapply H102 | .. ] | .. ] | .. ] | .. ] | .. ] | intros H103 H104 H105 H106 H107 H108; [apply H109 in H107; [apply H109 in H108; [eapply H36; [apply H112 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Definition aforallZ {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.
Lemma Hoare_conj : forall c P1 P2 Q1 Q2, ⦃ P1 ⦄ c ⦃ Q1 ⦄ -> ⦃ P2 ⦄ c ⦃ Q2 ⦄ -> ⦃ P1 //\\ P2 ⦄ c ⦃ Q1 //\\ Q2 ⦄ .
Proof.
custom0 c P1 P2 Q1 Q2 H H0 Hoare_skip_inv Hoare_consequence_post Hoare_skip P1 P2 Q1 Q2 H H0 Hoare_assign_inv Hoare_consequence_pre Hoare_assign aupdate P1 P2 Q1 Q2 H H0 Hoare_seq_inv H H0 P1 P2 Q1 Q2 H H0 Hoare_ifthenelse_inv H H0 Hoare_ifthenelse P1 P2 Q1 Q2 H H0 Hoare_while_inv H H0 P1 P2 Q1 Q2 H H0 Hoare_assert_inv H H0 Hoare_consequence P1 P2 Q1 Q2 H H0 Hoare_havoc_inv Hoare_havoc.
- apply Hoare_seq with ( R1 //\\ R2 ).
-- auto.
-- auto.
- eapply Hoare_consequence with ( P := Inv1 //\\ Inv2 ).
-- custom26 Hoare_while Hoare_consequence_pre IHc.
-- Tauto.
-- Tauto.
- eapply Hoare_assert with ( P := R1 //\\ R2 ).
- Tauto.
- Tauto.
- unfold aupdate, aforall in *. Tauto.
Qed.

Lemma Hoare_disj:
  forall c P1 P2 Q1 Q2,
  ⦃ P1 ⦄ c ⦃ Q1 ⦄ -> ⦃ P2 ⦄ c ⦃ Q2 ⦄ ->
  ⦃ P1 \\// P2 ⦄ c ⦃ Q1 \\// Q2 ⦄.
  Proof.
  custom0 c P1 P2 Q1 Q2 H H0 Hoare_skip_inv Hoare_consequence_post Hoare_skip P1 P2 Q1 Q2 H H0 Hoare_assign_inv Hoare_consequence_pre Hoare_assign aupdate P1 P2 Q1 Q2 H H0 Hoare_seq_inv H H0 P1 P2 Q1 Q2 H H0 Hoare_ifthenelse_inv H H0 Hoare_ifthenelse P1 P2 Q1 Q2 H H0 Hoare_while_inv H H0 P1 P2 Q1 Q2 H H0 Hoare_assert_inv H H0 Hoare_consequence P1 P2 Q1 Q2 H H0 Hoare_havoc_inv Hoare_havoc.
   - apply Hoare_seq with ( R1 \\// R2 ).
     -- auto.
     -- auto.
   - eapply Hoare_consequence with ( P := Inv1 \\// Inv2 ).
     -- custom26 Hoare_while Hoare_consequence_pre IHc.
     -- Tauto.
     -- Tauto.
   - eapply Hoare_assert with ( P := R1 \\// R2 ).
   - Tauto.
   - Tauto.
   - unfold aupdate, aforall in *; Tauto.
Qed.

Definition choice_axiom :=
  forall (A B: Type) (R: A -> B -> Prop),
  (forall a, exists b, R a b) ->
  exists f: A -> B, forall a, R a (f a).

 Ltac custom8 H0 H1 H2 H4 H3 :=  apply H0; [intros H1; [specialize ( H2 H1 ); [apply H4 in H3; [tauto] | .. ] | .. ] | .. ].
 Ltac custom25 H0 H1 H2 H3 :=  intros H0 ( H1 & H2 ); [exists H1; [custom5 H3 | .. ] | .. ].
 Ltac custom30 H0 H1 H2 H3 H4 :=  custom11 H0; [intros H1 ( H2 & H3 & H4 ); [exists H3; [custom4  | .. ] | .. ] | .. ].
 Ltac custom37 H0 H1 :=  exists H0; [apply H1; [custom4  | .. ] | .. ].
 Ltac custom52 H0 :=  exists H0; [auto | .. ].

Lemma Hoare_exists:
  choice_axiom ->
  forall (X: Type) c (P Q: X -> assertion),
  (forall x, ⦃ P x ⦄ c ⦃ Q x ⦄) ->
  ⦃ aexists P ⦄ c ⦃ aexists Q ⦄.
  Proof.
  intros CHOICE X c. induction c; intros P Q H.
  - assert (H': forall x, P x -->> Q x) by (intros; apply Hoare_skip_inv; auto).
    eapply Hoare_consequence_pre. apply Hoare_skip.
    custom25 s x Px H'.
  - assert (H': forall y, P y -->> aupdate x a (Q y)).
      intros. apply Hoare_assign_inv. auto.
    eapply Hoare_consequence_pre. apply Hoare_assign.
    custom25 s y Py H'.
  - set (REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x)).
    assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
      apply CHOICE. intros x. apply Hoare_seq_inv. auto.
    destruct H' as (R & H').
    apply Hoare_seq with (aexists R).
    apply IHc1. intros; apply H'.
    apply IHc2. intros; apply H'.
   - assert ( H1 : Hoare ( aexists ( fun x => atrue b //\\ P x ) ) c1 ( aexists Q ) ).
     -- custom8 IHc1 x H Hoare_ifthenelse_inv H.
     -- assert ( H2 : Hoare ( aexists ( fun x => afalse b //\\ P x ) ) c2 ( aexists Q ) ).
       --- custom8 IHc2 x H Hoare_ifthenelse_inv H.
       --- apply Hoare_ifthenelse.
         ---- custom30 Hoare_consequence_pre s A x B.
         ---- custom30 Hoare_consequence_pre s A x B.
  - set (REL := fun (x : X) (Inv: assertion) => Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x)).
    assert (H': exists Inv: X -> assertion, forall x: X, REL x (Inv x)).
      apply CHOICE. intros x. apply Hoare_while_inv. auto.
    destruct H' as (Inv & H').
    eapply Hoare_consequence with (P := aexists Inv).
    apply Hoare_while.
    apply Hoare_consequence_pre with (P := aexists (fun x => atrue b //\\ Inv x)).
    apply IHc. intros x. apply H'.
    -- intros s ( A & x & B ). exists x. custom4.
    -- custom25 s x A H'.
    -- intros s ( A & x & B ). custom37 x H'.
  - intros.
    set (REL := fun (x : X) (R: assertion) => (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x)).
    assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
      apply CHOICE. intros x. apply Hoare_assert_inv. auto.
    destruct H' as (R & A).
    eapply Hoare_consequence.
    apply Hoare_assert with (P := aexists R).
    -- intros s ( x & Px ). destruct ( A x ) as ( B & C ). apply B in Px. destruct Px as [  H1 H0 ]. custom31. custom52 x.
    -- intros s ( Bs & x & Rx ). destruct ( A x ) as ( B & C ). custom37 x C.
   - assert (H': forall y, P y -->> aforall (fun n => aupdate x (CONST n) (Q y))).
    intros. apply Hoare_havoc_inv. auto.
    eapply Hoare_consequence_pre. apply Hoare_havoc.
    custom25 s y Py H'.
Qed.


Ltac custom2 H0 H16 H17 H18 H22 H23 H24 H25 H26 H2 H1 H28 H29 H30 H31 H32 H33 H19 H6 H5 H47 H34 H20 H36 H37 H35 H48 H40 H41 H39 H4 H42 H38 H3 H43 H44 H45 H46 :=  induction H0; [intros H16 H17 H18; [assert ( H' : forall x, H16 x -->> H17 x ) by ( intros ; apply Hoare_skip_inv ; auto ); [eapply H22; [apply H23 | .. ] | .. ] | .. ] | intros H24 H25 H26; [assert ( H' : forall y, H24 y -->> aupdate H2 H1 ( H25 y ) ); [intros H28; [apply H29; [auto | .. ] | .. ] | eapply H22; [apply H30 | .. ] | .. ] | .. ] | intros H31 H32 H33; [set ( REL := fun ( x : H19 ) ( R : assertion ) => Hoare ( H31 x ) H6 R /\ Hoare R H5 ( H32 x ) ); [assert ( H' : exists R : H19 -> assertion, forall x : H47, H34 x ( R x ) ); [apply H20; [intros H36; [apply H37; [auto | .. ] | .. ] | .. ] | destruct H35 as ( R & H48 ); [apply H40 with ( H41 H39 ); [apply H4; [intros H42; [apply H38 | .. ] | .. ] | apply H3; [intros H43; [apply H38 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H44 H45 H46 | .. ].
Ltac custom3 H0 H20 H21 H22 H1 H2 H23 H24 H25 H3 H4 H26 H5 H6 H27 H28 H29 H7 H8 H9 H79 H10 H11 H30 H12 H13 H80 H14 H15 H16 H17 H31 H18 H19 H32 H33 H34 H35 H47 H48 H49 H45 H91 H51 H52 H53 H46 H55 H56 H57 H92 H50 H59 H44 H93 H58 H63 H64 H65 H94 H60 H67 H68 H69 H62 H66 H95 H72 H71 H73 H74 H75 H76 H77 H43 H78 H70 :=  custom2 H0 H20 H21 H22 H1 H2 H23 H24 H25 H3 H4 H26 H5 H6 H27 H28 H29 H7 H8 H9 H79 H10 H11 H30 H12 H13 H80 H14 H15 H16 H17 H31 H18 H19 H32 H33 H34 H35; [ |  |  | intros H55 H56 H57; [set ( REL := fun ( x : H7 ) ( Inv : assertion ) => Hoare ( atrue H44 //\\ Inv ) H0 Inv /\ ( H55 x -->> Inv ) /\ ( afalse H93 //\\ Inv -->> H56 x ) ); [assert ( H' : exists Inv : H7 -> assertion, forall x : H94, H60 x ( Inv x ) ); [apply H11; [intros H74; [apply H76; [auto | .. ] | .. ] | .. ] | destruct H66 as ( Inv & H95 ); [eapply H63 with ( H55 := H72 H71 ); [apply H75; [apply H1 with ( H55 := H72 ( fun x => H77 H44 //\\ H71 x ) ); [apply H43; [intros H78; [apply H70 | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | intros H47 H48 H49; [set ( REL := fun ( x : H7 ) ( R : assertion ) => ( H47 x -->> atrue H45 //\\ R ) /\ ( atrue H91 //\\ R -->> H48 x ) ); [assert ( H' : exists R : H7 -> assertion, forall x : H92, H50 x ( R x ) ); [apply H11; [intros H67; [apply H73; [auto | .. ] | .. ] | .. ] | destruct H58 as ( R & A ); [eapply H63; [apply H68 with ( H47 := H69 H62 ) | .. ] | .. ] | .. ] | .. ] | .. ] | intros H51 H52 H53; [assert ( H' : forall y, H51 y -->> aforall ( fun n => aupdate H46 ( CONST n ) ( H52 y ) ) ); [intros H59; [apply H65; [auto | .. ] | .. ] | eapply H1; [apply H64 | .. ] | .. ] | .. ] | .. ].
Ltac custom58 H0 H1 H2 H3 :=  intros H0 H1 H2; [custom5 H3 | .. ].
Ltac custom39 H0 H1 H2 H3 H4 :=  custom11 H0; [intros H1 ( H2 & H3 ) H4; [custom4  | .. ] | .. ].
Ltac custom66 H0 :=  apply H0; [custom4  | .. ].
Ltac custom67 H0 H1 H8 :=  destruct ( H0 H1 ) as ( B & C ); [custom5 H8].
Lemma Hoare_forall:
  choice_axiom ->
  forall (X: Type) (inhabited: X) c (P Q: X -> assertion),
  (forall x, ⦃ P x ⦄ c ⦃ Q x ⦄) ->
  ⦃ aforall P ⦄ c ⦃ aforall Q ⦄.
  Proof.
  intros CHOICE X inhabited c; induction c; intros P Q H.
  - assert (H': forall x, P x -->> Q x) by (intros; apply Hoare_skip_inv; auto).
    eapply Hoare_consequence_pre. apply Hoare_skip.
    custom59 s Ps x H'. apply Ps.
  - assert (H': forall y, P y -->> aupdate x a (Q y)).
    intros. apply Hoare_assign_inv. auto.
    eapply Hoare_consequence_pre. apply Hoare_assign.
    custom58 s Ps y H'.
  - set (REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x)).
    assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
    apply CHOICE. intros x. apply Hoare_seq_inv. auto.
    destruct H' as (R & H').
    apply Hoare_seq with (aforall R).
    apply IHc1. intros; apply H'.
    apply IHc2. intros; apply H'.
  - assert ( H1 : Hoare ( aforall ( fun x => atrue b //\\ P x ) ) c1 ( aforall Q ) ).
    -- custom8 IHc1 x H Hoare_ifthenelse_inv H.
    -- assert ( H2 : Hoare ( aforall ( fun x => afalse b //\\ P x ) ) c2 ( aforall Q ) ).
      --- custom8 IHc2 x H Hoare_ifthenelse_inv H.
      --- apply Hoare_ifthenelse.
        ---- custom39 Hoare_consequence_pre s A B x.
        ---- custom39 Hoare_consequence_pre s A B x.
- set (REL := fun (x : X) (Inv: assertion) => Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x)).
    assert (H': exists Inv: X -> assertion, forall x: X, REL x (Inv x)).
      apply CHOICE. intros x. apply Hoare_while_inv. auto.
    destruct H' as (Inv & H').
    eapply Hoare_consequence with (P := aforall Inv).
    apply Hoare_while.
    apply Hoare_consequence_pre with (P := aforall (fun x => atrue b //\\ Inv x)).
    apply IHc. intros x. apply H'.
  -- intros s [ A B ] x. custom4.
  -- custom58 s A x H'.
  -- intros s [ A B ] x. custom66 H'.
- intros.
  set (REL := fun (x : X) (R: assertion) => (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x)).
  assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
    apply CHOICE. intros x. apply Hoare_assert_inv. auto.
  destruct H' as (R & A).
  eapply Hoare_consequence.
  apply Hoare_assert with (P := aforall R).
  -- intros s Pall. split.
     --- custom67 A inhabited B.
     --- intros x. custom67 A x B.
  -- intros s ( Bs & Rall ) x. destruct ( A x ) as ( B & C ). custom66 C.
- assert (H': forall y, P y -->> aforall (fun n => aupdate x (CONST n) (Q y))).
  intros. apply Hoare_havoc_inv. auto.
  eapply Hoare_consequence_pre. apply Hoare_havoc.
  intros s Pall n y. custom5 H'.
Qed.

(** ** 2.4. Soundness *)

(** *** Soundness of Hoare logic, in the style of type soundness proofs. *)

Module Soundness1.

Lemma Hoare_safe:
  forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  forall s, P s -> ~(error c s).
Proof.
  induction 1; intros s Ps; simpl; auto. destruct Ps. red in H. congruence.
Qed.

Ltac custom28 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [inv H4 | .. ].
Ltac custom56 H0 H1 H2 H3 H4 H5 :=  custom28 H0 H1 H2 H3 H4; [custom16 H5 | .. ].
Ltac custom38 H0 :=  custom11 H0; [eauto | .. ].
Ltac custom43 H0 H1 H2 :=  custom16 H0; [custom12 H1 H2 | auto | .. ].
Ltac custom46 H0 H1 :=  split; [ | unfold H0, H1; [auto | .. ] | .. ].
Ltac custom61 H0 H1 :=  destruct ( beval H0 H1 ); [auto | .. ].
Lemma Hoare_step : forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> forall s c' s', P s -> red ( c, s ) ( c', s' ) -> exists P', ⦃ P' ⦄ c' ⦃ Q ⦄ /\ P' s' .
Proof.
   induction 1.
    - custom28 s c' s' Ps RED.
    - custom56 s c' s' Ps RED P.
      -- constructor.
      -- exact Ps.
    - custom56 s c' s' Ps RED Q.
      -- assumption.
      -- custom38 Hoare_skip_inv.
      -- destruct ( IHHoare1 _ _ _ Ps H2 ) as ( P' & HO' & Ps' ). custom43 P' Hoare_seq Q.
    - custom28 s c' s' Ps RED. exists ( if beval b s' then atrue b //\\ P else afalse b //\\ P ). split.
      -- custom61 b s'. auto.
      -- unfold aand, atrue, afalse. destruct ( beval b s' ) eqn : B.
        --- auto.
        --- auto.
    - custom28 s c' s' Ps RED.
      -- exists ( afalse b //\\ P ). custom46 aand afalse. constructor.
      -- exists ( atrue b //\\ P ). custom46 aand atrue. custom53 Hoare_seq P. custom5 Hoare_while.
    - custom56 s c' s' Ps RED Q.
      -- constructor.
      -- apply Ps.
    - intros s c' s' Ps RED. destruct Ps as [ Ps1 Ps2 ]. inv RED. exists ( atrue b //\\ P ). split.
      -- constructor.
      -- custom4.
    - intros s c' s' Ps RED. apply H0 in Ps. destruct ( IHHoare _ _ _ Ps RED ) as ( R & HO & Rs' ). custom43 R Hoare_consequence_post Q.
Qed.

Corollary Hoare_steps : forall P Q c s c' s', ⦃ P ⦄ c ⦃ Q ⦄ -> P s -> star red ( c, s ) ( c', s' ) -> exists P', ⦃ P' ⦄ c' ⦃ Q ⦄ /\ P' s' .
Proof.
   assert ( REC : forall cs cs', star red cs cs' -> forall P Q, Hoare P ( fst cs ) Q -> P ( snd cs ) -> exists P', Hoare P' ( fst cs' ) Q /\ P' ( snd cs' ) ).
    - induction 1.
      -- intros P Q H H0. custom52 P.
      -- intros P Q H1 H2. destruct a as [ c1 s1 ], b as [ c2 s2 ], c as [ c3 s3 ]. simpl in *. destruct ( Hoare_step _ _ _ H1 _ _ _ H2 H ) as ( R & HO & Rs2 ). custom38 IHstar.
    - intros P Q c s c' s' H H0 H1. eapply ( REC ( c, s ) ( c', s' ) ).
      -- eauto.
      -- eauto.
      -- eauto.
Qed.

Corollary Hoare_sound : forall P c Q s, ⦃ P ⦄ c ⦃ Q ⦄ -> P s -> ~ goeswrong c s /\ ( forall s', terminates c s s' -> Q s' ) .
Proof.
   intros P c Q s HO Ps. split.
    - intros ( c' & s' & RED & STUCK ). destruct ( Hoare_steps _ _ _ _ _ _ HO Ps RED ) as ( P' & HO' & Ps' ). custom38 Hoare_safe. eauto.
    - intros s' ( c' & RED & TERM ). red in TERM. subst c'. destruct ( Hoare_steps _ _ _ _ _ _ HO Ps RED ) as ( P' & HO' & Ps' ). custom38 Hoare_skip_inv.
Qed.

End Soundness1.

(** *** Soundness of strong Hoare logic, using an inductive "safe" predicate. *)

Module Soundness2.

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c: com) (s s': store) : Prop :=
  exists c', star red (c, s) (c', s') /\ terminated c'.

Definition goeswrong (c: com) (s: store) : Prop :=
  exists c' s', star red (c, s) (c', s') /\ error c' s'.

Inductive safe (Q: assertion): com -> store -> Prop :=
  | safe_now: forall c s,
      terminated c -> Q s ->
      safe Q c s
  | safe_step: forall c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
      safe Q c s.

Definition Triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "〚〚 P 〛〛 c 〚〚 Q 〛〛" := (Triple P c Q) (at level 90, c at next level).

Ltac custom1 H0 H1 H2 H3 H4 :=  apply H0; [unfold H1; [congruence | .. ] | cbn | intros H2 H3 H4; [inv H4 | .. ] | .. ].
Ltac custom21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 :=  intros H0 H1 H2 H3 H4; [custom1 H5 H6 H7 H8 H9; [tauto | apply H10; [reflexivity | exact H4 | .. ] | .. ] | .. ].
Ltac custom34 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3; [reflexivity | auto | .. ] | .. ].

Lemma Triple_skip : forall P, 〚〚 P 〛〛 SKIP 〚〚 P 〛〛 .
Proof.
   custom34 P s PRE safe_now.
Qed.

Lemma Triple_assign : forall P x a, 〚〚 aupdate x a P 〛〛 ASSIGN x a 〚〚 P 〛〛 .
Proof.
   custom21 P x a s PRE safe_step terminated c' s' RED safe_now.
Qed.

Ltac custom63 H0 H1 H2 H3 H4 :=  custom1 H0 H1 H2 H3 H4; [auto | .. ].
Ltac custom18 H0 H1 H2 H3 H4 :=  apply H0; [unfold H1; [congruence | .. ] | cbn; [auto | .. ] | intros H2 H3 H4 | .. ].
Remark safe_seq : forall ( Q R : assertion ) ( c' : com ), ( forall s, Q s -> safe R c' s ) -> forall c s, safe Q c s -> safe R ( c ;; c' ) s .
Proof.
   intros Q R c2 QR. induction 1.
    - rewrite H. custom63 safe_step terminated c' s' RED.
      -- custom5 QR.
      -- inv H2.
    - custom18 safe_step terminated c' s' RED. inv RED.
      -- elim H. custom7.
      -- custom5 H2.
Qed.

Ltac custom1 H0 H1 H2 H3 H4 :=  apply H0; [unfold H1; [congruence | .. ] | cbn | intros H2 H3 H4; [inv H4 | .. ] | .. ].
Ltac custom41 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 :=  intros H0 H1 H2 H3 H4 H5 H6; [intros H7 H8; [custom12 H9 H1 | .. ] | .. ].
Lemma Triple_seq : forall P Q R c1 c2, 〚〚 P 〛〛 c1 〚〚 Q 〛〛 -> 〚〚 Q 〛〛 c2 〚〚 R 〛〛 -> 〚〚 P 〛〛 c1 ;; c2 〚〚 R 〛〛.
Proof.
   custom41 P Q R c1 c2 H H0 s PRE safe_seq.
Qed.

Ltac custom10 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 :=  intros H0 H1 H2 H3 H4 H5 H6; [intros H7 H8; [custom1 H9 H10 H11 H12 H13; [auto | destruct ( beval H2 H12 ) eqn : B; [apply H5; [custom4  | .. ] | apply H6; [custom4  | .. ] | .. ] | .. ] | .. ] | .. ].
Lemma Triple_ifthenelse : forall P Q b c1 c2, 〚〚 atrue b //\\ P 〛〛 c1 〚〚 Q 〛〛 -> 〚〚 afalse b //\\ P 〛〛 c2 〚〚 Q 〛〛 -> 〚〚 P 〛〛 IFTHENELSE b c1 c2 〚〚 Q 〛〛 .
Proof.
   custom10 P Q b c1 c2 H H0 s PRE safe_step terminated c' s' RED.
Qed.

Ltac custom23 H0 H1 :=  eapply H0; [eexact H1 | .. ].
Ltac custom68 H0 H1 H2 H3 :=  apply H0 with ( H1 H2 H3 ); [ | auto | .. ].
Lemma Triple_while : forall P variant b c, ( forall v, 〚〚 atrue b //\\ aequal variant v //\\ P 〛〛 c 〚〚 alessthan variant v //\\ P 〛〛 ) -> 〚〚 P 〛〛 WHILE b c 〚〚 afalse b //\\ P 〛〛 .
Proof.
   intros P variant b c T. assert ( REC : forall v s, P s -> aeval variant s = v -> safe ( afalse b //\\ P ) ( WHILE b c ) s ).
    - intro v. induction v using ( well_founded_induction ( Z.lt_wf 0 ) ). intros s H0 H1. custom63 safe_step terminated c' s' RED.
      -- apply safe_now.
        --- custom7.
        --- custom4.
      -- apply safe_seq with ( alessthan variant ( aeval variant s' ) //\\ P ).
        --- intros s'' [ PRE1 PRE2 ]. red in PRE1. custom23 H PRE1.
          ---- exact PRE2.
          ---- auto.
        --- apply T. custom31. split.
          ---- custom7.
          ---- auto.
    - intros s PRE. custom68 REC aeval variant s. auto.
Qed.

Ltac custom15 H0 H1 H2 H3 H4 H5 H6 H7 H8 :=  intros H0 H1; [intros H2 H3; [custom1 H4 H5 H6 H7 H8; [auto | constructor; [custom7  | apply H3 | .. ] | .. ] | .. ] | .. ].
Lemma Triple_havoc : forall x Q, 〚〚 aforall ( fun n => aupdate x ( CONST n ) Q ) 〛〛 HAVOC x 〚〚 Q 〛〛 .
Proof.
   custom15 x Q s PRE safe_step terminated c' s' RED.
Qed.

Ltac custom13 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H14 :=  intros H0 H1; [intros H2 [ H3 H4 ]; [custom1 H5 H6 H7 H8 H9; [red in H3; [congruence] | apply H14; [custom7  | custom4  | .. ] | .. ] | .. ] | .. ].
Lemma Triple_assert : forall b P, 〚〚 atrue b //\\ P 〛〛 ASSERT b 〚〚 atrue b //\\ P 〛〛 .
Proof.
   custom13 b P s PRE1 PRE2 safe_step terminated c' s' RED safe_now.
Qed.

Ltac custom45 H0 H1 H2 H3 H4 H5 H6 H7 H9 H10 :=  intros H0 H1 H2 H3 H4 H5 H6 H7; [assert ( REC : forall H4 s, safe H1 H9 s -> safe H3 H10 s ); [ | custom7  | .. ] | .. ].
Ltac custom60 H0 :=  custom22 H0; [auto | .. ].

Lemma Triple_consequence : forall P Q P' Q' c, 〚〚 P 〛〛 c 〚〚 Q 〛〛 -> P' -->> P -> Q -->> Q' -> 〚〚 P' 〛〛 c 〚〚 Q' 〛〛 .
Proof.
intros.
assert (REC: forall c s, safe Q c s -> safe Q' c s).
  induction 1.
- custom22 safe_now.
- custom60 safe_step.
- custom7.
Qed.

Theorem HOARE_sound : forall P c Q, 〚 P 〛 c 〚 Q 〛 -> 〚〚 P 〛〛 c 〚〚 Q 〛〛 .
Proof.
   induction 1.
    - apply Triple_skip.
    - apply Triple_assign.
    - custom12 Triple_seq Q.
    - custom22 Triple_ifthenelse.
    - custom53 Triple_while a.
    - apply Triple_havoc.
    - apply Triple_assert.
    - apply Triple_consequence with P Q.
      -- auto.
      -- auto.
      -- auto.
Qed.

End Soundness2.

(** *** Soundness of weak Hoare logic, using a coinductive "safe" predicate. *)

Module Soundness3.

CoInductive safe (Q: assertion): com -> store -> Prop :=
  | safe_now: forall c s,
      terminated c -> Q s ->
      safe Q c s
  | safe_step: forall c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
      safe Q c s.


Lemma safe_terminated_inv : forall Q c s, safe Q c s -> terminated c -> Q s .
Proof.
   intros Q c s H H0. inv H.
    - auto.
    - contradiction.
Qed.

Lemma safe_not_stuck : forall Q c s, safe Q c s -> ~ terminated c -> ~ ( error c s ) .
Proof.
   intros Q c s H H0. inv H.
    - contradiction.
    - auto.
Qed.

Lemma safe_step_inv : forall Q c s c' s', safe Q c s -> red ( c, s ) ( c', s' ) -> safe Q c' s' .
Proof.
   intros Q c s c' s' H H0. inv H.
    - red in H1. subst c. inv H0.
    - eauto.
Qed.

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄" := (triple P c Q) (at level 90, c at next level).

Ltac custom34 H0 H1 H2 H3 :=  intros H0 H1 H2; [apply H3; [reflexivity | auto | .. ] | .. ].
Lemma triple_skip : forall P, ⦃⦃ P ⦄⦄ SKIP ⦃⦃ P ⦄⦄ .
Proof.
   custom34 P s PRE safe_now.
Qed.

Lemma triple_assign : forall P x a, ⦃⦃ aupdate x a P ⦄⦄ ASSIGN x a ⦃⦃ P ⦄⦄ .
Proof.
   custom21 P x a s PRE safe_step terminated c' s' RED safe_now.
Qed.
Lemma triple_seq : forall P Q R c1 c2, ⦃⦃ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ -> ⦃⦃ Q ⦄⦄ c2 ⦃⦃ R ⦄⦄ -> ⦃⦃ P ⦄⦄ c1 ; ; c2 ⦃⦃ R ⦄⦄ .
Proof.
   custom41 P Q R c1 c2 H H0 s PRE safe_seq.
Qed.
Lemma triple_while : forall P b c, ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ -> ⦃⦃ P ⦄⦄ WHILE b c ⦃⦃ afalse b //\\ P ⦄⦄ .
Proof.
   intros P b c T. assert ( REC : forall s, P s -> safe ( afalse b //\\ P ) ( WHILE b c ) s ).
    - intros s Ps. custom18 safe_step terminated c' s' RED. inversion RED.
      -- apply safe_now.
        --- custom7.
        --- custom65.
      -- apply safe_seq with P.
        --- custom74 s'' Ps'' CHR.
        --- apply T. custom65.
    - custom74 s PRE REC.
Qed.
Lemma triple_ifthenelse : forall P Q b c1 c2, ⦃⦃ atrue b //\\ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ -> ⦃⦃ afalse b //\\ P ⦄⦄ c2 ⦃⦃ Q ⦄⦄ -> ⦃⦃ P ⦄⦄ IFTHENELSE b c1 c2 ⦃⦃ Q ⦄⦄ .
Proof.
   custom10 P Q b c1 c2 H H0 s PRE safe_step terminated c' s' RED.
Qed.
Lemma triple_havoc : forall x Q, ⦃⦃ aforall ( fun n => aupdate x ( CONST n ) Q ) ⦄⦄ HAVOC x ⦃⦃ Q ⦄⦄ .
Proof.
   custom15 x Q s PRE safe_step terminated c' s' RED.
Qed.
Lemma triple_assert : forall b P, ⦃⦃ atrue b //\\ P ⦄⦄ ASSERT b ⦃⦃ atrue b //\\ P ⦄⦄ .
Proof.
   custom13 b P s PRE1 PRE2 safe_step terminated c' s' RED safe_now.
Qed.
Lemma triple_consequence : forall P Q P' Q' c, ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> P' -->> P -> Q -->> Q' -> ⦃⦃ P' ⦄⦄ c ⦃⦃ Q' ⦄⦄ .
Proof.
   custom45 P Q P' Q' c H H0 H1 c c. destruct 1 as [  H3 H2 s c0 | H4 H3 H2 s c0 ].
    - custom22 safe_now.
    - custom60 safe_step.
Qed.
Lemma safe_mono : forall Q n c s, safe Q n c s -> forall n', ( n' <= n ) % nat -> safe Q n' c s .
Proof.
   induction 1.
    - intros n' H. replace n' with O by lia. constructor.
    - custom35 n' H1 safe_now.
    - custom35 n' H3 safe_step. custom58 c' s' H4 H2. lia.
Qed.
Lemma safe_now' : forall ( Q : assertion ) n c s, terminated c -> Q s -> safe Q n c s .
Proof.
   intros Q n c s H H0. destruct n as [  | ].
    - constructor.
    - custom22 safe_now.
Qed.
Lemma safe_notstuck : forall Q n c s, safe Q ( S n ) c s -> ~ error c s .
Proof.
   custom28 Q n c s H.
    - rewrite H1. cbn. auto.
    - auto.
Qed.
Lemma terminated_dec : forall c, { terminated c } + { ~ terminated c } .
Proof.
   unfold terminated. destruct c as [  | a x | c2 c1 | c2 c1 b | c b | b | x ].
    - ( left ; reflexivity ) ( left ; reflexivity ).
    - .
    - ( right ; discriminate ( left ; reflexivity ) ( left ; reflexivity ) || ( right ; discriminate ( left ; reflexivity ) ( left ; reflexivity ) || ( right ; discriminate ( left ; reflexivity ) || ( right ; discriminate ))|| ( right ; discriminate ))|| ( right ; discriminate )).
    - .
    - ( right ; discriminate ).
Qed.
Lemma sem_wp_seq : forall c1 c2 Q s, sem_wp ( c1 ; ; c2 ) Q s -> sem_wp c1 ( sem_wp c2 Q ) s .
Proof.
   unfold sem_wp. intros c1 c2 Q s SAFE. destruct ( terminated_dec c1 ) as [  t | n ].
    - custom5 safe_now. custom11 safe_step_inv. rewrite t. constructor.
    - custom5 safe_step.
      -- change ( ~ ( error ( c1 ; ; c2 ) s ) ). custom40 safe_not_stuck terminated.
      -- custom59 c' s' H CH. custom64 safe_step_inv SAFE.
Qed.
Lemma Hoare_sem_wp : forall c Q, ⦃ sem_wp c Q ⦄ c ⦃ Q ⦄ .
Proof.
   intro c. induction c.
    - custom54 Q Hoare_consequence_pre Hoare_skip s W. custom23 safe_terminated_inv W. custom7.
    - custom54 Q Hoare_consequence_pre Hoare_assign s W. assert ( W' : safe Q SKIP ( update x ( aeval a s ) s ) ).
      -- custom51 safe_step_inv W red_assign.
      -- custom48 safe_terminated_inv W'. cbn in NOTSTUCK.
    - intros Q. custom68 Hoare_seq sem_wp c2 Q. custom70 Hoare_consequence_pre IHc1. custom55 s sem_wp_seq.
    - custom55 Q Hoare_ifthenelse.
      -- custom9 Hoare_consequence_pre IHc1 s P1 P2 c1 b c1 c2 safe_step_inv.
      -- custom49 Hoare_consequence_pre IHc2 s P1 P2. replace c2 with ( if beval b s then c1 else c2 ).
        --- custom36 safe_step_inv P2.
        --- custom62 P1.
    - custom19 Q Hoare_consequence_post Hoare_while.
      -- custom49 Hoare_consequence_pre IHc s P1 P2. apply sem_wp_seq. custom36 safe_step_inv P2. exact P1.
      -- intros s [ P1 P2 ]. custom71 safe_terminated_inv. custom51 safe_step_inv P2 red_while_done. exact P1.
    - custom54 Q Hoare_consequence Hoare_assert s SAFE.
      -- assert ( NOTSTUCK : ~ ( error ( ASSERT b ) s ) ).
        --- custom40 safe_not_stuck terminated.
        --- assert ( B : beval b s = true ).
          ---- custom61 b s. auto.
          ---- assert ( FINAL : Q s ).
            ----- custom71 safe_terminated_inv. custom64 safe_step_inv SAFE.
            ----- custom69 FINAL. exact B.
      -- intros s. unfold aand. tauto.
    - custom19 Q Hoare_consequence_pre Hoare_havoc. intros s W n. assert ( W' : safe Q SKIP ( update x n s ) ).
      -- custom51 safe_step_inv W red_havoc.
      -- custom48 safe_terminated_inv W'.
Qed.
Theorem Hoare_complete : forall P c Q, ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> ⦃ P ⦄ c ⦃ Q ⦄ .
Proof.
   intros P c Q H. apply Hoare_consequence_pre with ( sem_wp c Q ).
    - apply Hoare_sem_wp.
    - custom55 s H.
Qed.
