Ltac custom0  := split; [ |auto | .. ].
Ltac custom1  := simpl; [split; [auto |auto | .. ] | .. ].
Ltac custom2  := simpl; [split; [discriminate 1 |inversion 1 | .. ] | .. ].
Ltac custom3  := split; [auto with arith |auto | .. ].
Ltac custom4 H0 H1 := simpl; [rewrite ( H0 H1 ); [split; [auto with arith |auto with arith | .. ] | .. ] | .. ].
Ltac custom5  := simpl; [split | .. ].
Ltac custom6  := split; [auto with arith | .. ].

