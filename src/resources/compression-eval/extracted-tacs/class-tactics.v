Ltac custom0 H0 H1 := apply H0; [intro H1 | .. ].
Ltac custom1 H0 H1 H2 H3 := intros H0 H1 H2 H3; [destruct ( H3 H1 ) as [ p | np ] | .. ].
Ltac custom2 H0 H1 H2 H3 H4 := intros H0 H1 H2 H3; [apply H0; [intro H4 | .. ] | .. ].
Ltac custom3 H0 H1 := unfold excluded_middle; [intros H0 H1 | .. ].
Ltac custom4 H0 H1 H2 := apply H0; [intro H1; [apply H2 | .. ] | .. ].
Ltac custom5 H0 H1 := unfold excluded_middle; [intros H0 H1; [apply H1 | .. ] | .. ].
Ltac custom6 H0 H1 := intro H0; [apply H1; [auto | .. ] | .. ].
