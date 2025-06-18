Ltac custom0  := rewrite inj_plus; [ring_simplify | .. ].
Ltac custom1 H0 H1 H2 H3 H4 H5 H6 H7 := intros H0 H1 H2; [case H0; [intros H3 H4 H5 H6 H7 | .. ] | .. ].
Ltac custom2  := split; [auto | .. ].
Ltac custom3 H0 := simpl; [intro H0; [case ( fraction H0 ); [inversion_clear 1; [split; [auto | .. ] | .. ] | .. ] | .. ] | .. ].
