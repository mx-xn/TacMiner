Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Hom.Yoneda.

Section LimitUniversalProperty.
  Context (J C : Category).
  Context (F : J ⟶ C).

  Definition ump_limit_construct (a z : C) (H : IsALimit F z) :
      ACone a F -> a ~> z.
  Proof.
    destruct H.
    intro m; specialize ump_limit with {| vertex_obj := a ; coneFrom := m |}.
    destruct ump_limit as [unique_obj ? ?].
    exact unique_obj.
  Defined.

  Proposition ump_limit_construct_proper (a z : C) (H : IsALimit F z) :
    Proper (equiv ==> equiv) (ump_limit_construct a z H).
  Proof.
    repeat(intro).
    unfold ump_limit_construct.
    apply uniqueness. simpl.
    intro j.
    set (k := (unique_property (ump_limit {| vertex_obj := a ; coneFrom := y |}))).
    destruct x, y; simpl in X.
    simpl in *; rewrite X; apply k.
  Qed.

  Local Arguments vertex_map {J C c F}.
  Proposition ump_limit_construct_recover (w z : C) (H : IsALimit F z) (m : obj[J])
     (a : ACone w F) : vertex_map limit_acone m ∘ (ump_limit_construct w z _ a) ≈ vertex_map a m.
  Proof.
    unfold ump_limit_construct. simpl. 
    exact (unique_property (ump_limit {| vertex_obj := w; coneFrom :=a |} ) _).
  Qed.

  Proposition ump_limit_construct_recover' (q w z : C) (H : IsALimit F z) (m : obj[J])
    (a : ACone w F) (f : q ~> w) :
    vertex_map limit_acone m ∘ (ump_limit_construct w z _ a ∘ f) ≈ vertex_map a m ∘ f.
  Proof.
    now rewrite comp_assoc, ump_limit_construct_recover.
  Qed.
  
  Create HintDb limit discriminated.
  Hint Resolve ump_limit_construct : limit.
  Hint Resolve ump_limit_construct_proper : limit.
  Hint Resolve vertex_map : limit.
  Hint Resolve limit_acone : limit.
  Hint Rewrite -> @cone_coherence : limit.
  Hint Rewrite -> ump_limit_construct_recover : limit.
  Hint Rewrite -> ump_limit_construct_recover' : limit.

  Proposition cone_equiv_to_morphism_equiv (c z : C) (H : IsALimit F z) (f g : c ~> z) :
    (forall a : J, vertex_map limit_acone a ∘ f ≈ vertex_map limit_acone a ∘ g) ->
    f ≈ g.
  Proof.
    intro e.
    set (C' := fmap[ConePresheaf F] f limit_acone).
    assert (A: (unique_obj (ump_limit {| vertex_obj := c ;  coneFrom := C'  |})) ≈ f) by
      (apply uniqueness; reflexivity).
    rewrite <- A.
    set (C'' := fmap[ConePresheaf F] g limit_acone).
    apply uniqueness.
    intro. simpl. symmetry. trivial.
  Qed.

  Ltac apply_cone_equiv_to_morphism_equiv :=
    match goal with
    | [ H : @IsALimit _ _ _ ?b |- @equiv _ (@homset _ _ ?b) _ _ ] =>
        simple eapply cone_equiv_to_morphism_equiv
    end.

  Hint Extern 2 => apply_cone_equiv_to_morphism_equiv : limit.
  Theorem cone_coherence_auto1 (x y : J) (f : x ~> y) (w z : C) (g : w ~> z)
    (A : ACone z F) :
    fmap[F] f ∘ (vertex_map A x ∘ g) ≈ vertex_map A y ∘ g.
  Proof.
    now rewrite comp_assoc, cone_coherence.
  Qed.

  Hint Rewrite -> cone_coherence_auto1 : limit.
  Hint Extern 20 => easy : core.

  Hint Extern 10 => (autorewrite with limit) : limit.
  
  Proposition LimitIsUniversalProperty :
    IsUniversalProperty C^op (fun c => IsALimit F c)
                            (fun c => @LimitSetoid J C F c).
  Proof.
    exists (@ConePresheaf J C F); intro c.
    repeat(unshelve econstructor; try intros); simpl in *.
    - auto with cat limit.
    - abstract(auto with cat limit).
    - abstract(auto with cat). 
    - abstract(auto with cat).
    - abstract(auto with cat).
    - auto with limit.
    - abstract(intros f g a; apply uniqueness; auto with limit).
    - abstract(auto with cat limit).
    - abstract(auto with cat limit).
    - abstract(auto with cat limit).
    - abstract(auto with cat limit).
    - abstract(auto with cat limit).
    - intros x1 x2. apply_cone_equiv_to_morphism_equiv. intro.
      autorewrite with limit.  rewrite <- X. now autorewrite with limit.
    - destruct X; apply to; exact id.
    - abstract(auto with cat limit).
    - destruct N; now apply X.
    - abstract(destruct X as [[X_to_transform X_to_nat ?]
                       [X_from_transform X_from_nat ?] iso_to_from ?]; simpl in *;
        rewrite X_to_nat; revert x;
      change _ with (X_to_transform vertex_obj[N]
                       (id{C} ∘ X_from_transform vertex_obj[N] coneFrom) ≈ (@coneFrom _ _ _ N));
      rewrite (proper_morphism (X_to_transform vertex_obj[N])
                   _ _(id_left (X_from_transform vertex_obj[N] coneFrom)));
      intro j;
               now rewrite (iso_to_from N (@coneFrom _ _ _ N) j), id_right).
    - abstract(destruct X as [[X_to_transform X_to_nat ?]
                       [X_from_transform X_from_nat ?] ? ?];
                simpl in *;
               set (k:= X_from_nat _ _ v (X_to_transform c id{C}));
               symmetry in k; rewrite iso_from_to, 2 id_left in k;
               rewrite <- k;
               apply (proper_morphism (X_from_transform vertex_obj[N]));
               simpl; intro j; symmetry; apply X0).
    - abstract(simpl; intros a b eq;
               destruct a, b as [to1 from1 tofrom1 fromto1];
               destruct eq as [eql eqr]; simpl in *;
               apply eql).
    - abstract(intros a f j; destruct x, to; simpl in *;
      rewrite naturality; revert j;
      change _ with (transform a (id{C} ∘ f) ≈ transform a f);
      now rewrite id_left). 
    - abstract(now unfold  ump_limit_construct).
    - abstract(auto with cat limit).
  Defined.

End LimitUniversalProperty.
      
      
      
      
