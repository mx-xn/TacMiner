
Require Import QArith Qcanon Qpower Qminmax.
 Ltac destr_zcompare := case Z.compare_spec; intros ?H.
 Ltac nzsimpl := autorewrite with nz in *. 
 Ltac nsubst :=
  match goal with E : _ _ = _ |- _ => rewrite E in * end.