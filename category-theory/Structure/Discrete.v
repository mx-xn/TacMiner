Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Import EqNotations.

(* A discrete category has no arrows except for identity morphisms. *)

Definition Discrete (C : Category) :=
  (* jww (2017-06-02): Equality is too much here. *)
  ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id.
