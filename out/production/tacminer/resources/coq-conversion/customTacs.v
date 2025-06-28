Ltac custom0 H0 := intros H0; [induction H0 | .. ].
Ltac custom1 e := induction e; [ |simpl |simpl | .. ].
Ltac custom2 H0 := simpl; [rewrite <- H0 | .. ].
Ltac custom3 e := induction e; [ |simpl | .. ].
Ltac custom4 := simpl; [lia | .. ].
Ltac custom5 e := induction e; [simpl |simpl | .. ].
Ltac custom6 := simpl; [auto | .. ].