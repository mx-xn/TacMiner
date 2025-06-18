Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section SymmetricMonoidal.

Context {C : Category}.

Class SymmetricMonoidal := {
  symmetric_is_braided : @BraidedMonoidal C;

  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

Coercion symmetric_is_braided : SymmetricMonoidal >-> BraidedMonoidal.

Context `{SymmetricMonoidal}.

Lemma hexagon_rotated {x y z} :
  tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ braid ∘ tensor_assoc ∘ braid.
Proof.
  rewrite <- (id_right (id ⨂ braid ∘ tensor_assoc ∘ braid)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ tensor_assoc braid);
  rewrite <- (comp_assoc _ (tensor_assoc ∘ braid) _).
  rewrite hexagon_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite braid_invol.
  cat.
Qed.

Lemma bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ braid ≈ braid ∘ f ⨂ g.
Proof.
  spose (braid_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

Lemma braid_bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  braid ∘ g ⨂ f ∘ braid ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_invol.
  cat.
Qed.

End SymmetricMonoidal.

Require Export Category.Structure.Monoidal.Balanced.

Program Definition balanced_twist_id_is_symmetric
  `{@BalancedMonoidal C}
  (to_twist : ∀ x : C, to twist ≈[C] to (@iso_id _ x)) :
  @SymmetricMonoidal C := {|
  braid_invol := _;
|}.
Next Obligation.
  pose proof (@balanced_to_commutes _ _ x y).
  rewrite <- to_twist.
  rewrite <- X; clear X.
  comp_left.
  rewrite <- id_left at 1.
  comp_right.
  rewrite !to_twist.
  now rewrite bimap_id_id.
Qed.

(* ncatlab: "Every symmetric monoidal category is balanced in a canonical way;
   in fact, the identity natural transformation (on the identity functor of
   BB) is a balance on BB if and only if BB is symmetric. Thus balanced
   monoidal categories fall between braided monoidal categories and symmetric
   monoidal categories." *)

Program Definition symmetric_is_balanced `{@SymmetricMonoidal C} :
  @BalancedMonoidal C := {|
  twist := @iso_id C
|}.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
