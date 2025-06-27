Sequences.vo Sequences.glob Sequences.v.beautified Sequences.required_vo: Sequences.v Ori_tacs.vo
Sequences.vio: Sequences.v Ori_tacs.vio
Sequences.vos Sequences.vok Sequences.required_vos: Sequences.v Ori_tacs.vos
Hoare.vo Hoare.glob Hoare.v.beautified Hoare.required_vo: Hoare.v Sequences.vo
Hoare.vio: Hoare.v Sequences.vio
Hoare.vos Hoare.vok Hoare.required_vos: Hoare.v Sequences.vos
Separation.vo Separation.glob Separation.v.beautified Separation.required_vo: Separation.v Ori_tacs.vo
Separation.vio: Separation.v Ori_tacs.vio
Separation.vos Separation.vok Separation.required_vos: Separation.v Ori_tacs.vos
Seplog.vo Seplog.glob Seplog.v.beautified Seplog.required_vo: Seplog.v Sequences.vo Separation.vo
Seplog.vio: Seplog.v Sequences.vio Separation.vio
Seplog.vos Seplog.vok Seplog.required_vos: Seplog.v Sequences.vos Separation.vos
Ori_tacs.vo Ori_tacs.glob Ori_tacs.v.beautified Ori_tacs.required_vo: Ori_tacs.v 
Ori_tacs.vio: Ori_tacs.v 
Ori_tacs.vos Ori_tacs.vok Ori_tacs.required_vos: Ori_tacs.v 
CSL.vo CSL.glob CSL.v.beautified CSL.required_vo: CSL.v Sequences.vo Separation.vo
CSL.vio: CSL.v Sequences.vio Separation.vio
CSL.vos CSL.vok CSL.required_vos: CSL.v Sequences.vos Separation.vos
Delay.vo Delay.glob Delay.v.beautified Delay.required_vo: Delay.v 
Delay.vio: Delay.v 
Delay.vos Delay.vok Delay.required_vos: Delay.v 
Monads.vo Monads.glob Monads.v.beautified Monads.required_vo: Monads.v Hoare.vo Separation.vo Delay.vo
Monads.vio: Monads.v Hoare.vio Separation.vio Delay.vio
Monads.vos Monads.vok Monads.required_vos: Monads.v Hoare.vos Separation.vos Delay.vos
