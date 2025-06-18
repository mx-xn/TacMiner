Require Import Category.Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Set Transparent Obligations.

Section Ty.

Inductive Ty : Set :=
  | TyUnit  : Ty
  | TyPair  : Ty → Ty → Ty
  | TyArrow : Ty → Ty → Ty.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

End Ty.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 41, right associativity) : Ty_scope.
