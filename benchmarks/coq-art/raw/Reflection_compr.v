Require Export ZArith.

Require Export List.

Require Export Arith.

Require Export Lia.

Require Export Zwf.

Require Export Relations.

Require Export Inverse_Image.

Require Export Transitive_Closure.

Require Export Zdiv.

Open Scope nat_scope.

Theorem verif_divide :
    forall m p:nat, 0 < m -> 0 < p ->
    (exists q:nat, m = q*p)->(Z_of_nat m mod Z_of_nat p = 0)%Z.
Proof. intros m p Hltm Hltp (q, Heq); rewrite Heq. rewrite inj_mult. replace (Z_of_nat q * Z_of_nat p)%Z with (0 + Z_of_nat q * Z_of_nat p)%Z; try ring. rewrite Z_mod_plus; auto. lia. Qed.

Theorem divisor_smaller :
    forall m p:nat, 0 < m -> forall q:nat, m = q*p -> q <= m.
Proof. intros m p Hlt; case p. - intros q Heq; rewrite Heq in Hlt; rewrite Nat.mul_comm in Hlt. elim (Nat.lt_irrefl 0);exact Hlt. - intros p' q; case q. + intros Heq; rewrite Heq in Hlt. elim (Nat.lt_irrefl 0);exact Hlt. + intros q' Heq; rewrite Heq. rewrite Nat.mul_comm; simpl; auto with arith. Qed.

Fixpoint check_range (v:Z)(r:nat)(sr:Z){struct r} : bool :=
  match r with
    O => true
  | S r' =>
    match (v mod sr)%Z with
      Z0 => false
    | _ => check_range v r' (Z.pred sr)
    end
  end.

Definition check_primality (n:nat) :=
  check_range (Z_of_nat n)(pred (pred n))(Z_of_nat (pred n)).

Fixpoint check_range' (v:Z)(r:nat){struct r} : bool :=
  match r with
    0 => true | 1 => true
  | S r' =>
      match (v mod Z_of_nat r)%Z with
      | 0%Z => false
      | _ => check_range' v r'
      end
  end.

Definition check_primality' (n:nat) :=
  check_range' (Zpos (P_of_succ_nat (pred n)))(pred (pred n)).

Theorem Zabs_nat_0 : forall x:Z, Z.abs_nat x = 0 -> (x = 0)%Z.
Proof. intros x; case x. - simpl; auto. - intros p Heq; elim (Nat.lt_irrefl 0). pattern 0 at 2; rewrite <- Heq. simpl; apply lt_O_nat_of_P. - intros p Heq; elim (Nat.lt_irrefl 0). pattern 0 at 2; rewrite <- Heq. simpl; apply lt_O_nat_of_P. Qed.

Ltac custom_tac3 H0 := intros H0; case H0.

Ltac custom_tac8  := simpl; auto.

Theorem Z_to_nat_and_back :
 forall x:Z, (0 <= x)%Z -> (Z.of_nat (Z.abs_nat x))=x.
Proof. custom_tac3 x. - auto. - intros p Hd; elim p. + unfold Z.abs_nat; intros p' Hrec; rewrite nat_of_P_xI. rewrite inj_S. rewrite inj_mult. rewrite Zpos_xI. unfold Z.succ. rewrite Hrec. custom_tac8 . + unfold Z.abs_nat. intros p' Hrec; rewrite nat_of_P_xO. rewrite inj_mult. rewrite Zpos_xO. unfold Z.succ. rewrite Hrec. custom_tac8 . + custom_tac8 . - intros p' Hd; elim Hd;auto. Qed.

Theorem check_range_correct :
  forall (v:Z)(r:nat)(rz:Z),
  (0 < v)%Z ->
  Z_of_nat (S r) = rz -> check_range v r rz = true ->
  ~ (exists k:nat, k <= (S r) /\ k <> 1 /\ 
                       (exists q:nat, Z.abs_nat v = q*k)).
Proof. intros v r; elim r. - intros rz Hlt H1 H2 Hex; case Hex; intros k; case k. + intros (Hle, (Hne1, (q, Heq))). rewrite Nat.mul_comm in Heq; simpl in Heq. rewrite (Zabs_nat_0 _ Heq) in Hlt. elim (Z.lt_irrefl 0); assumption. + intros k' (Hle, (Hne1, (q, Heq))). inversion Hle. assert (H':k'=0). * assumption. * rewrite H' in Hne1; elim Hne1;auto. * assert (H': S k' <= 0) by assumption. inversion H'. - intros r' Hrec rz Hlt H1 H2 Hex; case Hex; intros k; case k. + intros (Hle, (Hne1, (q, Heq))). rewrite Nat.mul_comm in Heq; simpl in Heq. rewrite (Zabs_nat_0 _ Heq) in Hlt. elim (Z.lt_irrefl 0); assumption. + intros k' (Hle, (Hne1, (q, Heq))). inversion Hle. rewrite <- H1 in H2. rewrite <- (Z_to_nat_and_back v) in H2. assert (Hmod:(Z_of_nat (Z.abs_nat v) mod Z.of_nat (S (S r')) = 0)%Z). * apply verif_divide. replace 0 with (Z.abs_nat 0%Z). apply Zabs_nat_lt. lia. simpl; auto. auto with arith. exists q. assert (H': k' = S r') by assumption. rewrite <- H';auto. * unfold check_range in H2. rewrite Hmod in H2; discriminate H2. * lia. * unfold check_range in H2; fold check_range in H2. case_eq ((v mod rz)%Z). intros Heqmod. rewrite Heqmod in H2. discriminate H2. intros pmod Heqmod; rewrite Heqmod in H2. elim (Hrec (Z.pred rz) Hlt). rewrite <- H1. rewrite inj_S. rewrite inj_S. rewrite inj_S. rewrite <- Zpred_succ. auto. assumption. exists (S k'). repeat split;auto. exists q; assumption. intros p Hmod. elim (Z_mod_lt v rz). rewrite Hmod. unfold Z.le; simpl; intros Hle'; elim Hle';auto. rewrite <- H1. rewrite inj_S. unfold Z.succ. generalize (Zle_0_nat (S r')). intros; lia. Qed.

Theorem nat_of_P_Psucc : 
 forall p:positive, nat_of_P (Pos.succ p) = S (nat_of_P p).
Proof. intros p; elim p. - simpl; intros p'; rewrite nat_of_P_xO. intros Heq; rewrite Heq; rewrite nat_of_P_xI; ring. - intros p' Heq; simpl. rewrite nat_of_P_xI. rewrite nat_of_P_xO;auto. - auto. Qed.

Theorem nat_to_Z_and_back:
 forall n:nat, Z.abs_nat (Z.of_nat n) = n.
Proof. intros n; elim n. - auto. - intros n'; simpl; case n'. + simpl; auto. + intros n''; simpl; rewrite nat_of_P_Psucc. intros Heq; rewrite Heq; auto. Qed.

Theorem check_correct :
  forall p:nat, 0 < p -> check_primality p = true ->
  ~(exists k:nat, k <> 1 /\ k <> p /\ (exists q:nat, p = q*k)).
Proof. unfold lt; intros p Hle; elim Hle. - intros Hcp (k, (Hne1, (Hne1bis, (q, Heq)))); rewrite Nat.mul_comm in Heq. assert (Hle' : k < 1). + elim (proj1 (Nat.lt_eq_cases k 1)); try(intuition; fail). apply divisor_smaller with (2:= Heq); auto. + case_eq k. intros Heq'; rewrite Heq' in Heq; simpl in Heq; discriminate Heq. intros; lia. - intros p' Hlep' Hrec; unfold check_primality. assert (H':(exists p'':nat, p' = (S p''))). + inversion Hlep'. exists 0; auto. eapply ex_intro;eauto. + elim H'; intros p'' Hp''; rewrite Hp''. repeat rewrite <- pred_Sn. intros Hcr Hex. elim check_range_correct with (3:= Hcr). rewrite inj_S; generalize (Zle_0_nat (S p'')). intros; lia. auto. elim Hex; intros k (Hne1, (HneSSp'', (q, Heq))); exists k. split. assert (HkleSSp'': k <= S (S p'')). * apply (divisor_smaller (S (S p'')) q). auto with arith. rewrite Nat.mul_comm. assumption. * lia. * split. assumption. exists q; now rewrite nat_to_Z_and_back. Qed.

Theorem prime_2333 :
 ~(exists k:nat, k <> 1 /\ k <> 2333 /\ (exists q:nat, 2333 = q*k)).
Proof. apply check_correct; auto with arith. (**Finished transaction in 132. secs (131.01u,0.62s)*) Qed.

Theorem reflection_test :
 forall x y z t u:nat, x+(y+z+(t+u)) = x+y+(z+(t+u)).
Proof. intros; repeat rewrite Nat.add_assoc; auto. Qed.

Inductive bin : Set := node : bin->bin->bin | leaf : nat->bin.

Fixpoint flatten_aux (t fin:bin){struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Compute 
  flatten
     (node (leaf 1) (node (node (leaf 2)(leaf 3)) (leaf 4))).

Fixpoint bin_nat (t:bin) : nat :=
  match t with
  | node t1 t2 => bin_nat t1 + bin_nat t2
  | leaf n => n
  end.

Eval lazy beta iota delta [bin_nat] in
 (bin_nat
   (node (leaf 1) (node (node (leaf 2) (leaf 3)) (leaf 4)))).

Theorem flatten_aux_valid :
 forall t t':bin, bin_nat t + bin_nat t' = bin_nat (flatten_aux t t').
Proof. intros t; elim t; simpl; auto. intros t1 IHt1 t2 IHt2 t'; rewrite <- IHt1; rewrite <- IHt2. rewrite Nat.add_assoc; trivial. Qed.

Theorem flatten_valid : forall t:bin, bin_nat t = bin_nat (flatten t).
Proof. intros t; elim t; simpl; auto. intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid; rewrite <- IHt2. trivial. Qed.

Theorem flatten_valid_2 :
  forall t t':bin, bin_nat (flatten t) = bin_nat (flatten t')->
  bin_nat t = bin_nat t'.
Proof. intros; rewrite (flatten_valid t); rewrite (flatten_valid t'); auto. Qed.

Theorem reflection_test' :
 forall x y z t u:nat, x+(y+z+(t+u))=x+y+(z+(t+u)).
Proof. intros. change (bin_nat (node (leaf x) (node (node (leaf y) (leaf z)) (node (leaf t)(leaf u)))) = bin_nat (node (node (leaf x)(leaf y)) (node (leaf z) (node (leaf t)(leaf u))))). apply flatten_valid_2; auto. Qed.

Ltac model v :=
  match v with
  | (?X1 + ?X2) =>
    let r1 := model X1 
              with r2 := model X2 in constr:(node r1 r2)
  | ?X1 => constr:(leaf X1)
  end.

Ltac assoc_eq_nat :=
  match goal with
  | [ |- (?X1 = ?X2 :>nat) ] =>
   let term1 := model X1 with term2 := model X2 in
   (change (bin_nat term1 = bin_nat term2);
    apply flatten_valid_2;
    lazy beta iota zeta delta [flatten flatten_aux bin_nat]; 
    auto)
  end.

Theorem reflection_test'' :
 forall x y z t u:nat, x+(y+z+(t+u)) = x+y+(z+(t+u)).
Proof. intros; assoc_eq_nat. Qed.

Section assoc_eq.

Variables (A : Type)(f : A->A->A)
  (assoc : forall x y z:A, f x (f y z) = f (f x y) z).

Fixpoint bin_A (l:list A)(def:A)(t:bin){struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l def t1)(bin_A l def t2)
  | leaf n => nth n l def
  end.

Theorem flatten_aux_valid_A :
 forall (l:list A)(def:A)(t t':bin),
 f (bin_A l def t)(bin_A l def t') = bin_A l def (flatten_aux t t').
Proof. intros l def t; elim t; simpl; auto. intros t1 IHt1 t2 IHt2 t'; rewrite <- IHt1; rewrite <- IHt2. symmetry; apply assoc. Qed.

Theorem flatten_valid_A :
 forall (l:list A)(def:A)(t:bin),
   bin_A l def t = bin_A l def (flatten t).
Proof. intros l def t; elim t; simpl; trivial. intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A; rewrite <- IHt2. auto. Qed.

Theorem flatten_valid_A_2 :
 forall (t t':bin)(l:list A)(def:A),
   bin_A l def (flatten t) = bin_A l def (flatten t')->
   bin_A l def t = bin_A l def t'.
Proof. intros t t' l def Heq. rewrite (flatten_valid_A l def t); now rewrite (flatten_valid_A l def t'). Qed.

End assoc_eq.

Ltac term_list f l v :=
  match v with
  | (f ?X1 ?X2) =>
    let l1 := term_list f l X2 in term_list f l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:(X2) in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => compute_rank tl (S n) v
    end
  end.

Ltac model_aux l f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := model_aux l f X1 with r2 := model_aux l f X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Ltac model_A A f def v :=
  let l := term_list f (nil (A:=A)) v in
  let t := model_aux l f v in
  constr:(bin_A A f l def t).

Ltac assoc_eq A f assoc_thm :=
  match goal with
  | [ |- (@eq A ?X1 ?X2) ] =>
  let term1 := model_A A f X1 X1 
  with term2 := model_A A f X1 X2 in
  (change (term1 = term2);
   apply flatten_valid_A_2 with (1 := assoc_thm); auto)
  end.

Theorem reflection_test3 :
 forall x y z t u:Z, (x*(y*z*(t*u)) = x*y*(z*(t*u)))%Z.
Proof. intros; assoc_eq Z Zmult Zmult_assoc. Qed.

Fixpoint nat_le_bool (n m:nat){struct m} : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n, S m => nat_le_bool n m
  end.

Fixpoint insert_bin (n:nat)(t:bin){struct t} : bin :=
  match t with
  | leaf m => match nat_le_bool n m with
              | true => node (leaf n)(leaf m)
              | false => node (leaf m)(leaf n)
              end
  | node (leaf m) t' => match nat_le_bool n m with
                        | true => node (leaf n) t
                        | false => 
                            node (leaf m)(insert_bin n t')
                        end
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t:bin) : bin :=
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.

Section commut_eq.

Variables (A : Type)(f : A->A->A).

Hypothesis comm : forall x y:A, f x y = f y x.

Hypothesis assoc : forall x y z:A, f x (f y z) = f (f x y) z.

Fixpoint bin_A' (l:list A)(def:A)(t:bin){struct t} : A :=
   match t with
   | node t1 t2 => f (bin_A' l def t1)(bin_A' l def t2)
   | leaf n => nth n l def
   end.

Theorem flatten_aux_valid_A' :
  forall (l:list A)(def:A)(t t':bin),
   f (bin_A' l def t)(bin_A' l def t') = bin_A' l def (flatten_aux t t').
Proof. intros l def t; elim t; simpl; auto. intros t1 IHt1 t2 IHt2 t'; rewrite <- IHt1; rewrite <- IHt2. symmetry; apply assoc. Qed.

Theorem flatten_valid_A' :
  forall (l:list A)(def:A)(t:bin),
    bin_A' l def t = bin_A' l def (flatten t).
Proof. intros l def t; elim t; simpl; trivial. intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A'; rewrite <- IHt2. trivial. Qed.

Theorem flatten_valid_A_2' :
 forall (t t':bin)(l:list A)(def:A),
   bin_A' l def (flatten t) = bin_A' l def (flatten t')->
   bin_A' l def t = bin_A' l def t'.
Proof. intros t t' l def Heq. rewrite (flatten_valid_A' l def t); rewrite (flatten_valid_A' l def t'). trivial. Qed.

Theorem insert_is_f : forall (l:list A)(def:A)(n:nat)(t:bin),
   bin_A' l def (insert_bin n t) = 
   f (nth n l def) (bin_A' l def t).
Proof. intros l def n t; elim t. intros t1; case t1. intros t1' t1'' IHt1 t2 IHt2. simpl. auto. intros n0 IHt1 t2 IHt2. simpl. case (nat_le_bool n n0). simpl. auto. simpl. rewrite IHt2. repeat rewrite assoc; rewrite (comm (nth n l def)); auto. simpl. intros n0. case (nat_le_bool n n0); auto; try rewrite comm; auto. Qed.

Theorem sort_eq : forall (l:list A)(def:A)(t:bin),
    bin_A' l def (sort_bin t) = bin_A' l def t.
Proof. intros l def t; elim t. intros t1 IHt1; case t1. auto. intros n t2 IHt2; simpl; rewrite insert_is_f. rewrite IHt2; auto. auto. Qed.

Theorem sort_eq_2 :
 forall (l:list A)(def:A)(t1 t2:bin),
   bin_A' l def (sort_bin t1) = bin_A' l def (sort_bin t2)->
   bin_A' l def t1 = bin_A' l def t2.
Proof. intros l def t1 t2. rewrite <- (sort_eq l def t1); rewrite <- (sort_eq l def t2). trivial. Qed.

End commut_eq.

Ltac term_list' f l v :=
  match v with
  | (f ?X1 ?X2) =>
    let l1 := term_list' f l X2 in term_list' f l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank' l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:(X2) in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => compute_rank' tl (S n) v
    end
  end.

Ltac model_aux' l f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := model_aux' l f X1 with r2 := model_aux' l f X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank' l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Ltac comm_eq' A f assoc_thm comm_thm :=
  match goal with
  | [ |- (?X1 = ?X2 :>A) ] =>
    let l := term_list' f (nil (A:=A)) X1 in
    let term1 := model_aux' l f X1 
    with term2 := model_aux' l f X2 in
    (change (bin_A' A f l X1 term1 = bin_A' A f l X1 term2);
      apply flatten_valid_A_2' with (1 := assoc_thm);
      apply sort_eq_2 with (1 := comm_thm)(2 := assoc_thm); 
      auto)
  end.

Theorem reflection_test4 : forall x y z:Z, (x+(y+z) = (z+x)+y)%Z.
Proof. intros x y z. comm_eq' Z Zplus Zplus_assoc Zplus_comm. Qed.

Section prime_sqrt.

Open Scope Z_scope.

Theorem div_Zsqrt :
 forall m n p:Z, 0 < m < n ->
  n=m*p-> 0 < m <= Z.sqrt n \/ 0 < p <= Z.sqrt n.
Proof. intros m n p Hint Heq. elim (Z_lt_le_dec (Z.sqrt n) m); elim (Z_lt_le_dec (Z.sqrt n) p). - intros Hltm Hltp. assert (Hlem : (Z.sqrt n)+1 <= m) by lia. assert (Hlep : (Z.sqrt n)+1 <= p) by lia. elim (Z.lt_irrefl n). apply Z.lt_le_trans with (((Z.sqrt n)+1)*((Z.sqrt n)+1)). assert (Hposn : 0 <= n) by lia. generalize (Z.sqrt_spec n Hposn);cbv zeta;intro H23. intuition. pattern n at 3; rewrite Heq. apply Zmult_le_compat; try lia. generalize (Z.sqrt_nonneg n). lia. generalize (Z.sqrt_nonneg n). lia. - intros Hple _; right; split; auto. apply Zmult_lt_0_reg_r with m; try tauto. rewrite Zmult_comm; lia. - intros _ Hmle; left; split; tauto. - intros _ Hmle; left; split; tauto. Qed.

Definition divides_bool (p t:Z) : bool :=
 match t mod p with
   0 => true
 | _ => false
 end.

Fixpoint test_odds (n:nat) (p t:Z) {struct n} : bool :=
 match n with
 | 0%nat => negb (divides_bool 2 t)
 | S n' =>
   if test_odds n' (p - 2) t then negb (divides_bool p t) else false
 end.

Definition prime_test (n:nat) : bool :=
 match n with
 | 0%nat => false
 | 1%nat => false
 | S (S n) => 
  let x := (Z_of_nat (S (S n))) in
  let s := (Z.sqrt x) in
  let (half_s, even_bit) :=
    match s with
    | Zpos(xI h) => (Zpos h, 0)
    | Zpos(xO h) => (Zpos h, 1)
    | Zpos xH => (0, 0)
    | _ => (0, 1)  
    end  in
  test_odds (Z.abs_nat half_s) (s + even_bit) x
 end.

Time Eval lazy beta iota delta zeta in (prime_test 2333).

Theorem test_odds_correct2 :
  forall n x:nat,
    (1 < x)%nat ->
  forall p:Z,
    test_odds n p (Z_of_nat x) = true ->
    ~(exists y:nat, x = y*2)%nat.
Proof. intros n; elim n. - unfold test_odds, divides_bool; intros x H1ltx _ Heq Hex. assert (Heq' : Z_of_nat x mod Z_of_nat 2 = 0). + apply verif_divide; auto with zarith. + simpl (Z_of_nat 2) in Heq'; rewrite Heq' in Heq; simpl in Heq; discriminate. - clear n; intros n IHn x H1ltx p; simpl. case_eq (test_odds n (p - 2) (Z_of_nat x)). + intros Htest' _; apply (IHn x H1ltx (p - 2)); auto. + intros; discriminate. Qed.

Theorem Z_of_nat_le :
  forall x y, Z_of_nat x <= Z_of_nat y -> (x <= y)%nat.
Proof. intros; lia. Qed.

Theorem test_odds_correct :
  forall (n x:nat)(p:Z),
   p = 2*(Z_of_nat n)+1 ->
   (1 < x)%nat -> test_odds n p (Z_of_nat x) = true -> 
   forall q:nat, (1 < q <= 2*n+1)%nat -> ~(exists y:nat, x = q*y)%nat.
Proof. induction n. - intros x p Hp1 H1ltx Hn q Hint. exfalso; lia. - intros x p Hp H1ltx; simpl (test_odds (S n) p (Z_of_nat x)); intros Htest q (H1ltq, Hqle). case_eq (test_odds n (p -2) (Z_of_nat x)). + intros Htest'true. rewrite Htest'true in Htest. unfold divides_bool in Htest. elim (proj1 (Nat.lt_eq_cases q (2*S n + 1)%nat) Hqle). * intros Hqlt. assert (Hqle': (q <= (2* S n))%nat) by lia. elim (proj1 (Nat.lt_eq_cases q (2 * S n)%nat) Hqle'). replace (2*S n)%nat with (2*n +2)%nat. intros Hqlt'. assert (Hqle'' : (q <= 2*n +1)%nat) by lia. apply (IHn x (p - 2)); auto with zarith arith; try (rewrite Hp; rewrite inj_S; unfold Z.succ); ring. ring. intros Hq (y, Hdiv); elim (test_odds_correct2 n x H1ltx (p - 2)); auto. exists (S n * y)%nat; rewrite Hdiv; rewrite Hq; ring. * intros Hq Hex; assert (Hp' : p = Z_of_nat q). rewrite Hp; rewrite Hq; rewrite inj_plus; rewrite inj_mult; auto. rewrite Hp' in Htest; rewrite (verif_divide x q) in Htest. simpl in Htest; discriminate. lia. lia. elim Hex; intros y Hdiv; exists y; rewrite Hdiv; ring. + intros Htest'; rewrite Htest' in Htest; simpl in Htest; discriminate. Qed.

Theorem lt_Zpos : forall p:positive, 0 < Zpos p.
Proof. intros p; elim p. - intros; rewrite Zpos_xI; lia. - intros; rewrite Zpos_xO; lia. - auto with zarith. Qed.

Theorem Zneg_lt : forall p:positive, Zneg p < 0.
Proof. intros p; elim p. - intros; rewrite Zneg_xI; lia. - intros; rewrite Zneg_xO; lia. - auto with zarith. Qed.

Theorem prime_test_correct :
 forall n:nat, prime_test n = true ->
 ~(exists k:nat, k <> 1 /\ k <> n /\ (exists q:nat, n = q*k))%nat.
Proof. intros n; case_eq n. - simpl; intros Heq Hd; discriminate. - intros n0; case_eq n0. + simpl; intros Heq1 Heq2 Hd; discriminate. + unfold prime_test; intros n1 Heqn0 Heqn. assert (H1ltn : (1 < n)%nat). * rewrite Heqn; auto with arith. * rewrite <- Heqn. lazy beta zeta delta [prime_test]. case_eq (Z.sqrt (Z_of_nat n)). intros Hsqrt_eq. elim (Zlt_asym 1 (Z_of_nat n)). lia. lapply (Z.sqrt_spec (Z_of_nat n)). rewrite Hsqrt_eq; simpl. lia. lia. intros p Hsqrt_eq Htest_eq (k, (Hn1, (Hnn, (q,Heq)))). assert (H0ltn:(0 < n)%nat) by lia. assert (Hkltn:(k < n)%nat). assert (Heq' : n=(k*q)%nat). rewrite Heq; ring. generalize (divisor_smaller n q H0ltn k Heq'). lia. assert (Hex: exists k':nat, (1 < (Z_of_nat k') <= (Z.sqrt (Z_of_nat n))) /\ (exists q':nat, n=(k'*q')%nat)). elim (div_Zsqrt (Z_of_nat k) (Z_of_nat n) (Z_of_nat q)). intros Hint1; exists k;split. lia. exists q; rewrite Heq; ring. intros Hint2; exists q; split. split. elim (Zle_or_lt (Z_of_nat q) 1); auto. intros hqle1; assert (Hq1: q = 1%nat). lia. rewrite Hq1 in Heq; simpl in Heq; elim Hnn; rewrite Heq; ring. tauto. exists k; auto. split. case_eq k. intros Hk0; rewrite Hk0 in Heq; rewrite Heq in H1ltn; rewrite Nat.mul_0_r in H1ltn; lia. intros; unfold Z.lt; simpl; auto. lia. rewrite Zmult_comm; rewrite <- inj_mult; rewrite Heq;auto. elim Hex; intros k' ((H1ltk', Hk'ltsqrt), Hex'); clear Hex. case_eq p. intros p' Hp; rewrite Hp in Htest_eq. elim (test_odds_correct (Z.abs_nat (Zpos p')) n (Zpos p)) with k'. rewrite Z_to_nat_and_back. rewrite Hp. auto with zarith. auto with zarith. auto. repeat rewrite Zminus_0_r in Htest_eq. rewrite Hp; auto. split. lia. apply Z_of_nat_le. rewrite inj_plus. rewrite inj_mult. rewrite Z_to_nat_and_back. simpl (Z_of_nat 2). simpl (Z_of_nat 1). rewrite <- Zpos_xI. rewrite <- Hp. rewrite <- Hsqrt_eq; auto. auto with zarith. auto. intros p' Hp; rewrite Hp in Htest_eq. elim (test_odds_correct (Z.abs_nat (Zpos p')) n (Zpos p + 1)) with k'. rewrite Z_to_nat_and_back. rewrite Hp; rewrite Zpos_xO; ring. generalize (lt_Zpos p'); intros; lia. auto. rewrite <- Hp in Htest_eq; auto. split. lia. apply Z_of_nat_le. rewrite inj_plus. rewrite inj_mult. rewrite Z_to_nat_and_back. simpl (Z_of_nat 2); simpl (Z_of_nat 1). rewrite <- Zpos_xO. rewrite <- Hp; lia. auto with zarith. auto. intros Hp; rewrite Hp in Hsqrt_eq. rewrite Hsqrt_eq in Hk'ltsqrt. lia. intros p Hsqrt_eq. elim (Zle_not_lt 0 (Z.sqrt (Z_of_nat n))). apply Z.sqrt_nonneg. rewrite Hsqrt_eq. apply Zneg_lt. Qed.

End prime_sqrt.

