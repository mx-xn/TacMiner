Ltac custom1 H0 H1 := destruct ( zlt H0 H1 ); [simpl | .. ].
Ltac custom2 H2 H3 := intros; [destruct ( zlt H2 H3 ); [simpl |intuition | .. ] | .. ].
Ltac custom3 := intros; [simpl | .. ].
Ltac custom4 := unfold mem , In; [intros | .. ].
Ltac custom5 H0 H1 := intros; [destruct ( zlt H0 H1 ); [ | .. ] | .. ].
Ltac custom6 := intros; [auto | .. ].
Ltac custom7 H1 H2 := intros; [destruct ( zlt H1 H2 ); [ | .. ] | .. ].
Ltac custom8 := split; [intros |intros | .. ].

