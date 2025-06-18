Ltac custom0 H0 H1 H2 := intros H0 H1 H2; [apply H0 | .. ].
Ltac custom1 H0 := apply H0; [assumption | .. ].
Ltac custom2 H0 H1 H2 := intros H0 H1 H2; [apply H0; [assumption | apply H1 | .. ] | .. ].
Ltac custom3 H0 H1 := apply H0; [assumption | assumption; [apply H1 | .. ] | .. ].