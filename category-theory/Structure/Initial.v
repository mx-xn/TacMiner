Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* To be initial is just to be terminal in the opposite category; but to avoid
   confusion, we'd like a set of notations specific to categories with initial
   objects. *)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

Definition initial_obj : C := @terminal_obj _ I.
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.
