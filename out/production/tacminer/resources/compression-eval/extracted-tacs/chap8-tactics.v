Ltac custom1 H0 H1 H2 := injection H0; [intros H1 H2 | .. ].
Ltac custom2  := simpl; [auto | .. ].
Ltac custom3 H0 := induction H0; [discriminate | .. ].
Ltac custom4  := apply ( Pfact1 1 1 ); [discriminate |apply Pfact0 | .. ].
Ltac custom5 H0 H1 H2 H3 H4 H5 H6 := intros H0 H1 H2 H3 H4; [injection H0; [intros H5 H6; [rewrite <- H5; [auto | .. ] | .. ] | .. ] | .. ].
Ltac custom6 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 := intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11; [injection H1; [intros H12 H13; [subst H8 H14; [eauto | .. ] | .. ] | .. ] | .. ].
