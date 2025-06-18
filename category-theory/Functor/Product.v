Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(* A product of functors over some object in a monoidal category. *)

#[export]
Program Instance Product
        {C : Category} {D : Category} `{@Monoidal D}
        {F : C ⟶ D} {G : C ⟶ D} : C ⟶ D := {
  fobj := fun x => (F x ⨂ G x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f
}.
Next Obligation.
  proper;
  apply bimap_respects;
  now apply fmap_respects.
Qed.
Next Obligation. normal; reflexivity. Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.
