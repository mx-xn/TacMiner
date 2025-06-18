Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Constant.

Generalizable All Variables.

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT T}.
Context `{@Constant D DT T}.

Class ConstantFunctor := {
  unmap_one : F 1 ~{D}~> 1;

  map_const {x : T} : constant_obj T x ~> F (constant_obj T x);

  fmap_constant (x : T) :
    fmap (constant x) ≈ @map_const x ∘ constant x ∘ unmap_one;
}.

End ConstantFunctor.
