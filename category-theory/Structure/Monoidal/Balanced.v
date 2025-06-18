Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section BalancedMonoidal.

Context {C : Category}.

Class BalancedMonoidal := {
  balanced_is_braided : @BraidedMonoidal C;

  twist {x} : x ≅ x;
  twist_natural : natural (@twist);

  balanced_to : to (@twist I) ≈ id;
  balanced_from : from (@twist I) ≈ id;

  balanced_to_commutes {x y} :
    braid ∘ twist ⨂ twist ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist;

  balanced_from_commutes {x y} :
    braid ∘ twist⁻¹ ⨂ twist⁻¹ ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist⁻¹;
}.
#[export] Existing Instance balanced_is_braided.

Coercion balanced_is_braided : BalancedMonoidal >-> BraidedMonoidal.

End BalancedMonoidal.
