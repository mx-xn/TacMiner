Ltac custom0 H0 H1 := apply H0; [apply H1; [assumption | .. ] | .. ].
Ltac custom1 H0 := apply H0; [assumption | .. ].
Ltac custom2 H0 H1 := intro H0; [apply H1 | .. ].
Ltac custom3 H0 H1 H2 := intro H0; [apply H1; [apply H2; [assumption | .. ] | .. ] | .. ].
