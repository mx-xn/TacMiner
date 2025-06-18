Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Dinatural.

Context {C : Category}.
Context `{@Terminal C}.
Context `{@Terminal (C^op)}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.
Context {G : C^op ∏ C ⟶ D}.

Definition prod_split {x y z w} (f : x ~{C^op}~> z) (g : y ~{C}~> w) :
  (x, y) ~{ (C ^op) ∏ C }~> (z, w) := (f, g).
Arguments prod_split {_ _ _ _} _ _ /.

Infix "⋆⋆⋆" := prod_split (at level 100) : category_scope.

Class Dinatural := {
  ditransform {x} : F (x, x) ~> G (x, x);

  dinaturality {x y} (f : x ~{C}~> y) :
    fmap[G] (op f ⋆⋆⋆ id) ∘ ditransform ∘ fmap[F] (id ⋆⋆⋆ f)
        ≈ fmap[G] (id ⋆⋆⋆ f) ∘ ditransform ∘ fmap[F] (op f ⋆⋆⋆ id)
}.

#[export] Program Instance Dinatural_Setoid : Setoid Dinatural.

End Dinatural.

Notation "ditransform[ F ]" := (@ditransform _ _ _ _ F)
  (at level 9, format "ditransform[ F ]") : category_scope.

(* Dinatural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion ditransform : Dinatural >-> Funclass.
