Require Import AllFloat.
Require Import Paux.
Require Import Zdivides.
Require Import Faux.
Require Import Option.
 
Theorem oZ1_oZ : forall o, oZ1 o = Z_of_nat (oZ o).
intros o; case o; simpl in |- *; auto.
intros x; apply sym_equal; apply inject_nat_convert; auto.
Qed.
Opaque Pdiv.
Opaque PdivBound.
 
Definition FindMin (bound base a : positive) (dexp exp : Z) :=
  match PdivBound bound a base with
  | ((q, r), n) =>
      match (exp + Z_of_nat n)%Z with
      | exp' =>
          match (dexp - exp')%Z with
          | Zpos e =>
              match q with
              | Some q1 =>
                  match Pdiv q1 (positive_exp base e) with
                  | (q', r') =>
                      (Float (oZ1 q') dexp,
                      Fplus (Zpos base) (Float (oZ1 r') exp')
                        (Float (oZ1 r) exp))
                  end
              | None => (Float 0 dexp, Float (oZ1 r) exp)
              end
          | _ => (Float (oZ1 q) exp', Float (oZ1 r) exp)
          end
      end
  end.
Section FminOp.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
 
Coercion Local FtoRradix := FtoR radix.
Variable b : Fbound.
Variable precision : nat.
Hypothesis precisionNotZero : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Let dExp := (- dExp b)%Z.
 
Theorem Zpower_nat_exp :
 forall (a : positive) (n : nat),
 exp (nat_of_P a) n = Zpower_nat (Zpos a) n :>Z.
intros a n; elim n; simpl in |- *; auto.
intros n0 H; rewrite Znat.inj_mult; rewrite H.
replace (S n0) with (1 + n0); [ rewrite Zpower_nat_is_exp | idtac ]; auto.
rewrite Zpower_nat_1; auto.
rewrite (inject_nat_convert (Zpos a)); auto.
Qed.
 
Definition Z2pos x :=
  match x with
  | Z0 => 1%positive
  | Zpos p => p
  | Zneg p => p
  end.
 
Theorem Z2pos_correct : forall z : Z, (0 < z)%Z -> Zpos (Z2pos z) = z.
intros z; case z; simpl in |- *; auto; unfold Zlt in |- *; simpl in |- *;
 intros; discriminate.
Qed.
 
Theorem FminOp_correct1 :
 forall a e,
 Float (Zpos a) e =
 (fst (FindMin (vNum b) (Z2pos radix) a dExp e) +
  snd (FindMin (vNum b) (Z2pos radix) a dExp e))%R :>R.
cut (1 < nat_of_P (Z2pos radix));
 [ intros Z2
 | apply lt_Zlt_inv; simpl in |- *; idtac;
    try rewrite (inject_nat_convert (Zpos (Z2pos radix)) (Z2pos radix)); 
    auto; rewrite Z2pos_correct; auto with zarith ].
intros a e; unfold FindMin in |- *.
generalize (PdivBound_correct1 (vNum b) a (Z2pos radix));
 case (PdivBound (vNum b) a (Z2pos radix)); simpl in |- *.
intros p; case p; simpl in |- *.
intros o1 o2 n H1.
CaseEq (dExp - (e + n))%Z; simpl in |- *.
intros H; unfold FtoRradix in |- *;
 rewrite <- (FshiftCorrect radix radixMoreThanOne n (Float (oZ1 o1) (e + n)));
 simpl in |- *; auto.
unfold Fshift in |- *; simpl in |- *; auto.
replace (e + n - n)%Z with e; [ idtac | auto with zarith ].
unfold FtoR in |- *; simpl in |- *; auto with arith.
rewrite <- Rmult_plus_distr_r; rewrite H1; auto.
rewrite plus_INR; rewrite INR_IZR_INZ; rewrite Znat.inj_mult.
rewrite Zpower_nat_exp; simpl in |- *.
rewrite Z2pos_correct; auto with zarith.
repeat rewrite oZ1_oZ; auto.
repeat rewrite <- INR_IZR_INZ; auto.
intros p0 H; generalize H1; clear H1; case o1.
intros x H1; generalize (Pdiv_correct x (positive_exp (Z2pos radix) p0));
 case (Pdiv x (positive_exp (Z2pos radix) p0)).
intros q' r'; simpl in |- *.
intros (H2, H3).
unfold FtoRradix in |- *;
 rewrite <-
  (FshiftCorrect radix radixMoreThanOne (Zabs_nat (n + Zpos p0))
     (Float (oZ1 q') dExp)); simpl in |- *; auto.
rewrite Z2pos_correct; auto with zarith.
rewrite Fplus_correct; auto with zarith.
rewrite <- (FshiftCorrect radix radixMoreThanOne n (Float (oZ1 r') (e + n)));
 simpl in |- *; auto.
unfold Fshift in |- *; simpl in |- *; auto.
replace (dExp - Zabs_nat (n + Zpos p0))%Z with e.
replace (e + n - n)%Z with e.
unfold FtoR in |- *; simpl in |- *; auto.
repeat rewrite <- Rmult_plus_distr_r; rewrite H1; simpl in |- *; auto.
rewrite H2.
rewrite positive_exp_correct.
repeat rewrite oZ1_oZ.
rewrite mult_plus_distr_r.
rewrite mult_assoc_reverse.
rewrite <- expPlus.
repeat rewrite plus_INR.
repeat (rewrite INR_IZR_INZ; rewrite Znat.inj_mult).
rewrite plus_comm.
repeat rewrite Zpower_nat_exp; simpl in |- *.
repeat rewrite Z2pos_correct; auto with zarith.
replace (Zabs_nat (n + Zpos p0)) with (n + nat_of_P p0); auto.
repeat rewrite <- INR_IZR_INZ; ring.
rewrite <- (inject_nat_convert (Zpos p0) p0); auto.
rewrite <- Znat.inj_plus.
apply sym_equal; apply absolu_INR.
ring.
rewrite <- (inject_nat_convert (Zpos p0) p0); auto.
rewrite <- Znat.inj_plus.
rewrite absolu_INR.
rewrite Znat.inj_plus.
rewrite (inject_nat_convert (Zpos p0) p0); auto.
rewrite <- H; ring.
auto with arith.
auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
intros H1; rewrite H1.
rewrite oZ1_oZ; repeat rewrite <- INR_IZR_INZ; ring.
apply lt_Zlt_inv; simpl in |- *; idtac;
 try rewrite (inject_nat_convert (Zpos (Z2pos radix)) (Z2pos radix)); 
 auto; rewrite Z2pos_correct; auto with zarith.
intros p0 H; unfold FtoRradix in |- *;
 rewrite <- (FshiftCorrect radix radixMoreThanOne n (Float (oZ1 o1) (e + n)));
 simpl in |- *; auto.
unfold Fshift in |- *; simpl in |- *; auto.
replace (e + n - n)%Z with e; [ idtac | auto with zarith ].
unfold FtoR in |- *; simpl in |- *; auto with arith.
rewrite <- Rmult_plus_distr_r; rewrite H1; auto.
rewrite plus_INR; rewrite INR_IZR_INZ; rewrite Znat.inj_mult.
rewrite Zpower_nat_exp; simpl in |- *.
repeat rewrite Z2pos_correct; auto with zarith.
repeat rewrite oZ1_oZ; auto.
repeat rewrite <- INR_IZR_INZ; auto.
Qed.
 
Theorem FminOp_correct2 :
 forall a e, (0 <= snd (FindMin (vNum b) (Z2pos radix) a dExp e))%R.
intros a e; unfold FindMin in |- *; case (PdivBound (vNum b) a (Z2pos radix)).
intros p; case p; simpl in |- *.
intros o1 o2 n; case (dExp - (e + n))%Z; simpl in |- *; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
replace 0%R with (0 * powerRZ radix e)%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real zarith.
case o2; simpl in |- *; auto with real.
intros p0; case o1; simpl in |- *.
intros o1'; case (Pdiv o1' (positive_exp (Z2pos radix) p0)); simpl in |- *;
 auto.
intros o o0.
repeat rewrite Z2pos_correct; auto with zarith.
unfold FtoRradix in |- *; rewrite Fplus_correct; auto with arith.
replace 0%R with (0 + 0)%R; [ idtac | ring ].
apply Rplus_le_compat; unfold FtoR in |- *; simpl in |- *; auto with real.
replace 0%R with (0 * powerRZ radix (e + n))%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
case o0; simpl in |- *; auto with real.
replace 0%R with (0 * powerRZ radix e)%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
case o2; simpl in |- *; auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *;
 replace 0%R with (0 * powerRZ radix e)%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
case o2; simpl in |- *; auto with real.
intros o; unfold FtoRradix, FtoR in |- *; simpl in |- *;
 replace 0%R with (0 * powerRZ radix e)%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
case o2; simpl in |- *; auto with real.
Qed.
 
Theorem FminOp_correct3 :
 forall a e, Fbounded b (fst (FindMin (vNum b) (Z2pos radix) a dExp e)).
cut (1 < nat_of_P (Z2pos radix));
 [ intros Z2
 | apply lt_Zlt_inv; simpl in |- *; idtac;
    try rewrite (inject_nat_convert (Zpos (Z2pos radix)) (Z2pos radix)); 
    auto; rewrite Z2pos_correct; auto with zarith ].
intros a e; unfold FindMin in |- *;
 generalize (PdivBound_correct2 (vNum b) a (Z2pos radix));
 case (PdivBound (vNum b) a (Z2pos radix)).
intros p; case p; simpl in |- *.
intros o1 o2 n H1.
CaseEq (dExp - (e + n))%Z; simpl in |- *.
intros H2; repeat (split; simpl in |- *; auto).
rewrite Zabs_eq;
 [ idtac
 | case o1; simpl in |- *; intros; red in |- *; simpl in |- *; auto;
    red in |- *; intros; discriminate ].
rewrite oZ1_oZ; rewrite <- (inject_nat_convert (Zpos (vNum b)) (vNum b));
 auto with zarith.
fold dExp in |- *; auto with zarith.
intros p0 H; generalize H1; clear H1; case o1; simpl in |- *.
intros x H1; generalize (Pdiv_correct x (positive_exp (Z2pos radix) p0));
 case (Pdiv x (positive_exp (Z2pos radix) p0)); simpl in |- *.
intros o o0 (H2, H3).
repeat (split; simpl in |- *; auto).
rewrite oZ1_oZ; rewrite <- (inject_nat_convert (Zpos (vNum b)) (vNum b));
 auto with zarith.
rewrite Zabs_eq; [ idtac | case o; simpl in |- *; auto with zarith ].
apply Znat.inj_lt.
apply le_lt_trans with (nat_of_P x); auto.
replace (oZ o) with (oZ o * 1 + 0); [ rewrite H2 | ring ].
apply plus_le_compat; auto with arith.
fold dExp in |- *; auto with zarith.
intros H1; repeat (split; simpl in |- *; auto with zarith).
intros p0 H; rewrite oZ1_oZ; repeat (split; simpl in |- *; auto).
rewrite Zabs_eq; [ idtac | case o1; simpl in |- *; auto with zarith ].
rewrite <- (inject_nat_convert (Zpos (vNum b)) (vNum b)); auto with zarith.
fold dExp in |- *; auto with zarith.
replace dExp with (e + n + (dExp - (e + n)))%Z; auto with zarith.
pattern (e + n)%Z at 3 in |- *; replace (e + n)%Z with (e + n + 0)%Z.
apply Zplus_le_compat; try rewrite H; auto with zarith.
auto with zarith.
Qed.
 
Theorem FminOp_correct4 :
 forall a e,
 snd (FindMin (vNum b) (Z2pos radix) a dExp e) = 0%R :>R \/
 Fcanonic radix b (fst (FindMin (vNum b) (Z2pos radix) a dExp e)).
intros a e; generalize (FminOp_correct3 a e); unfold FindMin in |- *;
 generalize (PdivBound_correct2 (vNum b) a (Z2pos radix));
 generalize (PdivBound_correct3 (vNum b) a (Z2pos radix));
 generalize (PdivBound_correct4 (vNum b) a (Z2pos radix));
 case (PdivBound (vNum b) a (Z2pos radix)).
cut (1 < nat_of_P (Z2pos radix));
 [ intros Z2
 | apply lt_Zlt_inv; simpl in |- *; idtac;
    try rewrite (inject_nat_convert (Zpos (Z2pos radix)) (Z2pos radix)); 
    auto; rewrite Z2pos_correct; auto with zarith ].
intros p; case p; simpl in |- *.
intros o1 o2 n H1 H2 H3.
CaseEq (dExp - (e + n))%Z; simpl in |- *.
intros H4 Fb; right.
cut (Fdigit radix (Float (oZ1 o1) (e + n)) <= precision);
 [ intros Le1 | idtac ].
case (le_lt_or_eq _ _ Le1); intros Le2.
right; repeat (split; simpl in |- *; auto).
fold dExp in |- *; auto with zarith.
case (Z_eq_dec (oZ1 o1) 0); intros Z3.
replace (radix * oZ1 o1)%Z with 0%Z; auto with zarith; rewrite Z3; ring.
rewrite pGivesBound; rewrite <- (Zabs_eq (Zpower_nat radix precision));
 auto with zarith.
apply (digit_anti_monotone_lt radix); auto.
replace (radix * oZ1 o1)%Z with (oZ1 o1 * Zpower_nat radix 1)%Z;
 [ idtac | rewrite Zpower_nat_1; ring ].
replace (Zpower_nat radix precision) with (1 * Zpower_nat radix precision)%Z;
 [ idtac | ring ].
repeat rewrite digitAdd; auto with zarith.
rewrite digit1; rewrite (fun x => plus_comm x 1); simpl in |- *;
 auto with arith.
left; repeat (split; simpl in |- *; auto).
rewrite Zabs_Zmult; rewrite (Zabs_eq radix); auto with zarith.
rewrite (PosNormMin radix b precision); auto with arith;
 unfold nNormMin in |- *.
apply Zle_Zmult_comp_l; auto with zarith.
rewrite <- Le2; unfold Fdigit in |- *; simpl in |- *; apply digitLess.
Contradict Le2; rewrite Le2; unfold Fdigit in |- *; simpl in |- *;
 auto with zarith.
apply pGivesDigit with (b := b); auto with arith.
intros p0 H; generalize H1 H2 H3; clear H1 H2 H3; case o1; simpl in |- *.
intros x H1 H2 H3;
 generalize (Pdiv_correct x (positive_exp (Z2pos radix) p0));
 case (Pdiv x (positive_exp (Z2pos radix) p0)); simpl in |- *.
intros o o0 H0 Fb; right.
cut (Fdigit radix (Float (oZ1 o) dExp) <= precision); [ intros Le1 | idtac ].
case (le_lt_or_eq _ _ Le1); intros Le2.
right; repeat (split; simpl in |- *; auto).
case (Z_eq_dec (oZ1 o) 0); intros Z3.
replace (radix * oZ1 o)%Z with 0%Z; auto with zarith; rewrite Z3; ring.
rewrite pGivesBound; rewrite <- (Zabs_eq (Zpower_nat radix precision));
 auto with zarith.
apply (digit_anti_monotone_lt radix); auto.
replace (radix * oZ1 o)%Z with (oZ1 o * Zpower_nat radix 1)%Z;
 [ idtac | rewrite Zpower_nat_1; ring ].
replace (Zpower_nat radix precision) with (1 * Zpower_nat radix precision)%Z;
 [ idtac | ring ].
repeat rewrite digitAdd; auto with zarith.
rewrite digit1; rewrite (fun x => plus_comm x 1); simpl in |- *;
 auto with arith.
left; repeat (split; simpl in |- *; auto).
rewrite Zabs_Zmult; rewrite (Zabs_eq radix); auto with zarith.
rewrite (PosNormMin radix b precision); auto with arith;
 unfold nNormMin in |- *.
apply Zle_Zmult_comp_l; auto with zarith.
rewrite <- Le2; unfold Fdigit in |- *; simpl in |- *; apply digitLess.
Contradict Le2; rewrite Le2; unfold Fdigit in |- *; simpl in |- *;
 auto with zarith.
apply pGivesDigit with (b := b); auto with arith.
intros H1 H2 H3; right; right;
 repeat (split; simpl in |- *; auto with zarith).
replace (radix * 0)%Z with 0%Z; [ auto with zarith | ring ].
intros p0 H Fb.
case (le_or_lt (nat_of_P (vNum b)) (nat_of_P a)); intros H4.
right; left.
repeat (split; simpl in |- *; auto).
rewrite Zabs_Zmult; repeat rewrite Zabs_eq; auto with zarith.
cut (nat_of_P (vNum b) <= (nat_of_P (Z2pos radix) * oZ o1)%nat)%Z;
 auto with zarith arith.
rewrite Znat.inj_mult;
 repeat rewrite (fun x => inject_nat_convert (Zpos x) x); 
 auto.
rewrite Z2pos_correct; auto; rewrite oZ1_oZ; auto.
apply Znat.inj_le; apply (H1 (Zabs_nat (nNormMin radix precision))); auto.
apply inject_nat_eq; rewrite Znat.inj_mult;
 repeat rewrite (fun x => inject_nat_convert (Zpos x) x); 
 auto.
rewrite Z2pos_correct; auto; rewrite inj_abs; auto with zarith.
apply PosNormMin; auto with zarith.
unfold nNormMin in |- *; auto with zarith.
case o1; simpl in |- *; auto; intros; red in |- *; intros; discriminate.
left; unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
generalize (H2 H4); intros tmp; injection tmp.
intros H'1 H'2 H'3; rewrite H'2; simpl in |- *; auto.
ring.
Qed.
 
Theorem FminOp_correct5 :
 forall a e,
 snd (FindMin (vNum b) (Z2pos radix) a dExp e) = 0%R :>R \/
 (snd (FindMin (vNum b) (Z2pos radix) a dExp e) <
  Fulp b radix precision (fst (FindMin (vNum b) (Z2pos radix) a dExp e)))%R.
cut (1 < nat_of_P (Z2pos radix));
 [ intros Z2
 | apply lt_Zlt_inv; simpl in |- *; idtac;
    try rewrite (inject_nat_convert (Zpos (Z2pos radix)) (Z2pos radix)); 
    auto; rewrite Z2pos_correct; auto with zarith ].
intros a e; case (FminOp_correct4 a e); auto; intros C1.
right; unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
unfold FindMin in |- *;
 generalize (PdivBound_correct (vNum b) a (Z2pos radix));
 case (PdivBound (vNum b) a (Z2pos radix)); simpl in |- *.
intros p; case p; simpl in |- *.
intros o1 o2 n H1.
CaseEq (dExp - (e + n))%Z; simpl in |- *.
intros H2; case H1.
apply lt_Zlt_inv; rewrite (fun x => inject_nat_convert (Zpos x) x); auto;
 try rewrite Z2pos_correct; auto with zarith.
intros tmp ((tmp1, H3), tmp2); rewrite oZ1_oZ; unfold FtoRradix, FtoR in |- *;
 simpl in |- *.
rewrite powerRZ_add; auto with real zarith.
rewrite (fun x y => Rmult_comm (powerRZ x y)).
apply Rlt_monotony_exp; auto with zarith.
rewrite <- Zpower_nat_powerRZ; auto with zarith.
rewrite <- (Z2pos_correct radix); try rewrite <- Zpower_nat_exp;
 auto with real zarith arith.
intros p0 H; generalize H1; clear H1; case o1.
intros x H1; generalize (Pdiv_correct x (positive_exp (Z2pos radix) p0));
 case (Pdiv x (positive_exp (Z2pos radix) p0)).
intros q' r'; simpl in |- *.
intros (H2, H3).
unfold Fplus in |- *; simpl in |- *.
replace (Zmin (e + n) e) with e.
replace (Zabs_nat (e + n - e)) with n.
replace (Zabs_nat (e - e)) with 0.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
repeat rewrite oZ1_oZ.
rewrite Z2pos_correct; auto with zarith.
replace dExp with (Zpos p0 + (e + n))%Z.
repeat (rewrite powerRZ_add; auto with real arith).
replace (powerRZ radix (Zpos p0) * (powerRZ radix e * powerRZ radix n))%R
 with (powerRZ radix (Zpos p0) * powerRZ radix n * powerRZ radix e)%R;
 [ idtac | ring ].
apply Rlt_monotony_exp; auto with arith.
replace (oZ o2 * Zpower_nat radix 0)%Z with (Z_of_nat (oZ o2)).
rewrite <- (inject_nat_convert (Zpos p0) p0); auto.
repeat rewrite <- Zpower_nat_powerRZ; auto with zarith.
replace radix with (Zpos (Z2pos radix)).
repeat rewrite <- Zpower_nat_exp; auto with zarith.
rewrite <- Rmult_IZR.
apply Rlt_IZR.
repeat rewrite <- Znat.inj_mult || rewrite <- Znat.inj_plus.
apply Znat.inj_lt.
apply
 lt_le_trans
  with
    (oZ r' * exp (nat_of_P (Z2pos radix)) n + exp (nat_of_P (Z2pos radix)) n).
case H1; auto with arith; intros tmp1 ((tmp2, H4), tmp3); auto with arith.
replace
 (oZ r' * exp (nat_of_P (Z2pos radix)) n + exp (nat_of_P (Z2pos radix)) n)
 with (S (oZ r') * exp (nat_of_P (Z2pos radix)) n).
apply lte_comp_mult; auto with arith.
rewrite positive_exp_correct in H3; auto with arith.
simpl in |- *; ring.
apply Z2pos_correct; auto.
rewrite Zpower_nat_O; idtac; simpl in |- *; auto with zarith.
auto with real zarith.
auto with real zarith.
rewrite <- H; ring.
replace (e - e)%Z with 0%Z; simpl in |- *; auto with zarith.
replace (e + n - e)%Z with (Z_of_nat n); simpl in |- *; auto with zarith.
apply sym_equal; apply absolu_INR.
ring.
apply sym_equal; apply Zmin_le2; auto with zarith.
auto with arith.
intros H1; case H1; auto with arith; intros H2 ((H3, H4), H5).
rewrite oZ1_oZ; unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
replace dExp with (Zpos p0 + (e + n))%Z.
repeat (rewrite powerRZ_add; auto with real arith).
replace (powerRZ radix (Zpos p0) * (powerRZ radix e * powerRZ radix n))%R
 with (powerRZ radix (Zpos p0) * powerRZ radix n * powerRZ radix e)%R;
 [ idtac | ring ].
apply Rlt_monotony_exp; auto with arith.
rewrite <- (inject_nat_convert (Zpos p0) p0); auto with arith.
replace radix with (Zpos (Z2pos radix)).
repeat rewrite <- Zpower_nat_powerRZ; auto with real zarith.
repeat rewrite <- Zpower_nat_exp; auto with zarith.
rewrite <- Rmult_IZR.
apply Rlt_IZR.
rewrite <- Znat.inj_mult.
apply Znat.inj_lt.
apply lt_le_trans with (1 * exp (nat_of_P (Z2pos radix)) n).
replace (1 * exp (nat_of_P (Z2pos radix)) n) with
 (exp (nat_of_P (Z2pos radix)) n); auto; ring.
apply lte_comp_mult; auto with arith.
elim (nat_of_P p0); simpl in |- *; auto with arith.
intros n0 H0; replace 1 with (1 * 1); auto with arith.
apply Z2pos_correct; auto with zarith.
auto with real zarith.
auto with real zarith.
rewrite <- H; ring.
intros p0 H; rewrite oZ1_oZ.
case H1; auto with arith; intros H2 ((H3, H4), H5).
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
repeat (rewrite powerRZ_add; auto with real arith).
replace (powerRZ radix e * powerRZ radix n)%R with
 (powerRZ radix n * powerRZ radix e)%R; [ idtac | ring ].
apply Rlt_monotony_exp; auto with arith.
replace radix with (Zpos (Z2pos radix)).
repeat rewrite <- Zpower_nat_powerRZ; auto with real zarith.
repeat rewrite <- Zpower_nat_exp; auto with real zarith arith.
apply Z2pos_correct; auto.
auto with real zarith arith.
Qed.
 
Theorem FminOp_correct6 :
 forall a e, (0 <= fst (FindMin (vNum b) (Z2pos radix) a dExp e))%R.
intros a e; unfold FindMin in |- *; case (PdivBound (vNum b) a (Z2pos radix)).
intros p; case p; simpl in |- *.
intros o1 o2 n; case (dExp - (e + n))%Z; simpl in |- *; auto.
rewrite oZ1_oZ; unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
replace 0%R with (0 * powerRZ radix (e + n))%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real zarith.
intros p0; case o1; simpl in |- *.
intros o1'; case (Pdiv o1' (positive_exp (Z2pos radix) p0)); simpl in |- *;
 auto.
intros o o0; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace 0%R with (0 * powerRZ radix dExp)%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
rewrite oZ1_oZ; rewrite <- INR_IZR_INZ; auto with real arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real arith.
intros o0; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace 0%R with (0 * powerRZ radix (e + n))%R; [ idtac | ring ].
apply Rmult_le_compat_r; auto with real arith.
rewrite oZ1_oZ; rewrite <- INR_IZR_INZ; auto with real arith.
Qed.
 
Theorem FSuccDiffPos :
 forall x : float,
 (0 <= x)%R ->
 Fminus radix (FSucc b radix precision x) x = Float 1%nat (Fexp x) :>R.
intros x H.
unfold FtoRradix in |- *; apply FSuccDiff1; auto with arith.
Contradict H; unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite H.
apply Rlt_not_le.
replace 0%R with (0 * powerRZ radix (Fexp x))%R; [ idtac | ring ].
apply Rlt_monotony_exp; auto with real arith.
generalize (nNormPos _ radixMoreThanOne precision);
 replace 0%R with (IZR (- 0%nat)); auto with real zarith arith.
Qed.
 
Theorem CanonicFulp :
 forall p : float,
 Fcanonic radix b p -> Fulp b radix precision p = Float 1%nat (Fexp p).
intros p H; unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
Qed.
 
Theorem FSuccUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 <= x)%R ->
 Fminus radix (FSucc b radix precision x) x = Fulp b radix precision x :>R.
intros x H H0; rewrite CanonicFulp; auto.
apply FSuccDiffPos; auto.
Qed.
 
Theorem FNSuccUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 <= x)%R ->
 Fminus radix (FNSucc b radix precision x) x = Fulp b radix precision x :>R.
intros x H H0.
unfold FNSucc in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
apply FSuccUlpPos; auto.
Qed.
 
Theorem FminOp_correct7 :
 forall a e,
 isMin b radix (Float (Zpos a) e)
   (fst (FindMin (vNum b) (Z2pos radix) a dExp e)).
intros a e; apply MinBinade with (precision := precision); auto with arith.
apply FminOp_correct3.
rewrite FminOp_correct1; fold FtoRradix in |- *; auto with real.
apply
 Rle_trans
  with (FtoRradix (fst (FindMin (vNum b) (Z2pos radix) a dExp e)) + 0)%R;
 auto with real.
generalize (FminOp_correct2 a e); auto with real.
rewrite FminOp_correct1; fold FtoRradix in |- *; auto with real.
case (FminOp_correct5 a e); intros H1.
rewrite H1; auto with real float.
apply
 Rle_lt_trans
  with (FtoRradix (fst (FindMin (vNum b) (Z2pos radix) a dExp e)));
 auto with real.
unfold FtoRradix in |- *; apply FNSuccLt; auto with arith.
case (FminOp_correct4 a e); intros H2.
rewrite H2; auto with real float.
apply
 Rle_lt_trans
  with (FtoRradix (fst (FindMin (vNum b) (Z2pos radix) a dExp e)));
 auto with real.
unfold FtoRradix in |- *; apply FNSuccLt; auto with arith.
cut (forall x y z, (y < z - x)%R -> (x + y < z)%R);
 [ intros th1; apply th1 | auto with real ].
unfold FtoR in |- *; rewrite <- (Fminus_correct radix); auto with arith.
rewrite FNSuccUlpPos; auto with arith.
apply FminOp_correct6; auto with arith.
intros x y z H; replace z with (x + (z - x))%R; auto with real.
Qed.
 
Inductive rResult : Set :=
  | rExact : float -> rResult
  | rRound : float -> rResult.
 
Definition rFloat o := match o with
                       | rExact e => e
                       | rRound e => e
                       end.
 
Definition rFloor (f : float) :=
  match f with
  | Float Z0 e => rExact (Float 0 dExp)
  | Float (Zpos a) e =>
      match FindMin (vNum b) (Z2pos radix) a dExp e with
      | (r1, Float Z0 _) => rExact r1
      | (r1, _) => rRound r1
      end
  | Float (Zneg a) e =>
      match FindMin (vNum b) (Z2pos radix) a dExp e with
      | (r1, Float Z0 _) => rExact (Fopp r1)
      | (r1, _) => rRound (Fopp (FSucc b radix precision r1))
      end
  end.
 
Theorem NotR0NotZero : forall f : float, Fnum f <> 0%Z -> f <> 0%R :>R.
intros f H; Contradict H; auto with float arith.
unfold FtoRradix, FtoR in H; simpl in H.
case (Rmult_integral _ _ H); intros H1.
2: Contradict H1; auto with real zarith.
apply eq_IZR; simpl in |- *; auto.
Qed.
 
Theorem rFloor_correct :
 forall f : float,
 isMin b radix f (rFloat (rFloor f)) /\
 match rFloor f with
 | rExact r => r = f :>R
 | rRound r => r <> f :>R /\ Fcanonic radix b r
 end.
intros f; case f.
intros a e; case a; auto.
simpl in |- *; split.
replace (FtoRradix (Float 0 e)) with (FtoRradix (Float 0 dExp)).
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := isMin b radix);
 auto with float.
apply MinRoundedModeP with (precision := precision); auto with arith.
repeat (split; simpl in |- *; auto with arith zarith).
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
intros p; generalize (FminOp_correct1 p e); generalize (FminOp_correct4 p e);
 generalize (FminOp_correct7 p e); simpl in |- *;
 case (FindMin (vNum b) (Z2pos radix) p dExp e); simpl in |- *; 
 auto.
intros f0 f1; case f1; simpl in |- *; auto.
intros a'; case a'; simpl in |- *; auto.
intros e' H1 H2 H3; split; auto; rewrite H3; unfold FtoRradix, FtoR in |- *;
 simpl in |- *; ring.
intros p' e' H1 H2 H3; split; auto.
split; auto.
Contradict H3; rewrite H3.
apply Rlt_not_eq; auto with real.
pattern (FtoRradix (Float (Zpos p) e)) at 1 in |- *;
 replace (FtoRradix (Float (Zpos p) e)) with
  (FtoRradix (Float (Zpos p) e) + 0)%R.
apply Rplus_lt_compat_l.
unfold FtoRradix, FtoR in |- *; simpl in |- *; apply Rmult_lt_0_compat;
 auto with real arith.
ring.
case H2; clear H2; auto; intros H2; Contradict H2.
apply NotR0NotZero; simpl in |- *; red in |- *; intros; discriminate.
intros p' e' H1 H2 H3; split; auto.
cut (Float (Zneg p') e' <> 0%R :>R); [ intros Rth1; split | idtac ].
Contradict H3; rewrite H3.
apply Rgt_not_eq; auto with real.
pattern (FtoRradix (Float (Zpos p) e)) at 1 in |- *;
 replace (FtoRradix (Float (Zpos p) e)) with
  (FtoRradix (Float (Zpos p) e) + 0)%R.
red in |- *; apply Rplus_lt_compat_l.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (- nat_of_P p' * powerRZ radix e')%R with
 (- (nat_of_P p' * powerRZ radix e'))%R; [ idtac | ring ].
replace 0%R with (-0)%R; [ idtac | ring ].
apply Ropp_lt_contravar; apply Rmult_lt_0_compat; auto with real arith.
ring.
case H2; auto; intros H4; Contradict Rth1; auto.
apply NotR0NotZero; simpl in |- *; red in |- *; intros; discriminate.
intros p;
 replace (FtoRradix (Float (Zneg p) e)) with
  (- FtoRradix (Float (Zpos p) e))%R.
2: rewrite <- (Fopp_correct radix); simpl in |- *; auto.
generalize (FminOp_correct1 p e); generalize (FminOp_correct3 p e);
 generalize (FminOp_correct4 p e); generalize (FminOp_correct5 p e);
 generalize (FminOp_correct6 p e); generalize (FminOp_correct7 p e);
 simpl in |- *; case (FindMin (vNum b) (Z2pos radix) p dExp e); 
 simpl in |- *; auto.
intros f0 f1; case f1; simpl in |- *; auto.
intros a'; case a'; simpl in |- *; auto.
intros Fexp H H0 H1 H2 H3 H4; split; auto.
apply MaxOppMin; auto.
replace (FtoRradix (Float (Zpos p) e)) with (FtoRradix f0).
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := isMax b radix);
 auto with float.
apply MaxRoundedModeP with (precision := precision); auto with arith.
rewrite H4; unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H4; rewrite (Fopp_correct radix); auto with arith;
 unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
intros p0 Fexp H H0 H1 H2 H3 H4;
 cut (FtoRradix (Float (Zpos p0) Fexp) <> 0%R :>R);
 [ intros Neq1; split | idtac ].
apply MaxOppMin; auto.
rewrite <-
 (FcanonicFormalizeEq _ radixMoreThanOne b precision)
  with (p := f0); auto with zarith.
change
  (isMax b radix (FtoRradix (Float (Zpos p) e)) (FNSucc b radix precision f0))
 in |- *.
apply MinMax; auto with arith.
rewrite H4.
Contradict Neq1.
replace 0%R with (FtoR radix f0 - f0)%R;
 [ rewrite <- Neq1 | fold FtoRradix in |- * ]; ring.
case H2; auto; intros H5; Contradict H5; apply NotR0NotZero; simpl in |- *;
 red in |- *; intros; discriminate. 
case H2; clear H2; intros H2; [ Contradict Neq1; auto | idtac ].
rewrite H4.
split.
apply Rlt_not_eq; auto with real.
rewrite (Fopp_correct radix); auto with arith.
apply Ropp_lt_contravar.
cut (forall x y z, (y < z - x)%R -> (x + y < z)%R);
 [ intros Rt1; apply Rt1 | idtac ].
unfold FtoRradix in |- *; rewrite <- Fminus_correct; auto with arith.
fold FtoRradix in |- *; rewrite (FSuccUlpPos f0); auto with arith.
case H1; auto; intros H5; Contradict H4; auto.
intros x y z H5; replace z with (x + (z - x))%R; auto with real; ring.
auto with float arith.
apply NotR0NotZero; simpl in |- *; red in |- *; intros; discriminate.
intros p0 Fexp H H0 H1 H2 H3 H4;
 cut (FtoRradix (Float (Zneg p0) Fexp) <> 0%R :>R);
 [ intros Neq1; split | idtac ].
apply MaxOppMin; auto.
rewrite <-
 (FcanonicFormalizeEq _ radixMoreThanOne b precision)
  with (p := f0); auto with zarith.
change
  (isMax b radix (FtoRradix (Float (Zpos p) e)) (FNSucc b radix precision f0))
 in |- *.
apply MinMax; auto with arith.
rewrite H4.
Contradict Neq1.
replace 0%R with (FtoR radix f0 - f0)%R;
 [ rewrite <- Neq1 | fold FtoRradix in |- * ]; ring.
case H2; auto; intros H5; Contradict H5; apply NotR0NotZero; simpl in |- *;
 red in |- *; intros; discriminate.
case H2; clear H2; intros H2; [ Contradict Neq1; auto | idtac ].
rewrite H4.
split.
apply Rlt_not_eq; auto with real.
rewrite (Fopp_correct radix); auto with arith.
apply Ropp_lt_contravar.
cut (forall x y z, (y < z - x)%R -> (x + y < z)%R);
 [ intros Rt1; apply Rt1 | idtac ].
unfold FtoRradix in |- *; rewrite <- Fminus_correct; auto with arith.
fold FtoRradix in |- *; rewrite (FSuccUlpPos f0); auto with arith.
case H1; auto; intros H5; Contradict H4; auto.
intros x y z H5; replace z with (x + (z - x))%R; auto with real; ring.
auto with float arith.
apply NotR0NotZero; simpl in |- *; red in |- *; intros; discriminate.
Qed.
 
Definition rCeil (f : float) :=
  match rFloor f with
  | rExact r => rExact r
  | rRound r => rRound (FSucc b radix precision r)
  end.
 
Theorem rCeil_correct :
 forall f : float,
 isMax b radix f (rFloat (rCeil f)) /\
 match rCeil f with
 | rExact r => r = f :>R
 | rRound r => r <> f :>R /\ Fcanonic radix b r
 end.
intros f; generalize (rFloor_correct f); unfold rCeil in |- *;
 case (rFloor f); simpl in |- *.
intros r (H1, H2); split; auto.
rewrite <- H2.
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := isMax b radix);
 auto with float.
apply MaxRoundedModeP with (precision := precision); auto with arith.
unfold isMin in H1; intuition.
intros r (H1, (H2, H3)); split; [ idtac | split ]; auto.
rewrite <- (FcanonicFormalizeEq _ radixMoreThanOne b precision) with (p := r);
 auto with zarith.
change (isMax b radix (FtoRradix f) (FNSucc b radix precision r)) in |- *.
apply MinMax; auto with arith.
Contradict H2; rewrite <- H2.
apply (MinUniqueP b radix) with (1 := H1).
rewrite <- H2.
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := isMin b radix).
apply MinRoundedModeP with (precision := precision); auto with arith.
apply FBoundedSuc; auto with arith.
apply FcanonicBound with (2 := H3); auto.
auto with float arith.
Qed.
 
Definition rToZero (f : float) :=
  match f with
  | Float Z0 e => rExact (Float 0 dExp)
  | Float (Zpos a) e => rFloor f
  | Float (Zneg a) e => rCeil f
  end.
 
Theorem rToZero_correct :
 forall f : float,
 ToZeroP b radix f (rFloat (rToZero f)) /\
 match rToZero f with
 | rExact r => r = f :>R
 | rRound r => r <> f :>R /\ Fcanonic radix b r
 end.
intros f; generalize (rFloor_correct f); generalize (rCeil_correct f);
 unfold rToZero in |- *; case f.
intros a e; case a; auto.
simpl in |- *; intros H H0; cut (Float 0 dExp = Float 0 e :>R);
 [ intros T1; split | idtac ]; auto.
rewrite <- T1; unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := ToZeroP b radix).
apply ToZeroRoundedModeP with (precision := precision); auto with arith.
repeat (split; simpl in |- *; auto with zarith).
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
intros p; case (rFloor (Float (Zpos p) e)).
intros f1 H1 (H2, H3); split; auto.
simpl in |- *; rewrite <- H3.
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := ToZeroP b radix).
apply ToZeroRoundedModeP with (precision := precision); auto with arith.
simpl in H2; case H2; auto.
intros f1 H1 (H2, H3); split; auto.
left; split; auto.
apply (LeFnumZERO radix); simpl in |- *; auto with zarith.
intros p; case (rCeil (Float (Zneg p) e)).
intros f1 (H2, H3) H1; split; auto.
simpl in |- *; rewrite <- H3.
unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdem with (b := b) (P := ToZeroP b radix).
apply ToZeroRoundedModeP with (precision := precision); auto with arith.
simpl in H2; case H2; auto.
intros f1 (H2, H3) H1; split; auto.
right; split; auto.
apply (LeZEROFnum radix); simpl in |- *; auto with zarith.
Qed.
 
Definition ZevenP a :=
  match Fnum a with
  | Z0 => true
  | Zpos (xO _) => true
  | Zneg (xO _) => true
  | _ => false
  end.
 
Theorem ZevenP_correct :
 forall a, match ZevenP a with
           | true => Feven a
           | false => Fodd a
           end.
intros a; case a; simpl in |- *.
intros n e; case n; unfold ZevenP, Feven, Fodd in |- *; simpl in |- *;
 auto with arith.
apply EvenO.
intros p; case p; simpl in |- *; simpl in |- *.
intros p1; exists (Zpos p1); rewrite BinInt.Zpos_xI; ring.
intros p1; exists (Zpos p1); rewrite BinInt.Zpos_xO; ring.
apply Odd1.
cut (forall x, Zneg x = (- Zpos x)%Z); [ intros th1 | simpl in |- *; auto ].
intros p; case p; simpl in |- *; simpl in |- *.
intros p1; exists (Zneg p1 + - (1))%Z; repeat rewrite th1;
 rewrite BinInt.Zpos_xI; ring.
intros p1; exists (Zneg p1); repeat rewrite th1; rewrite BinInt.Zpos_xO; ring.
exists (- (1))%Z; repeat rewrite th1; ring.
Qed.
 
Theorem Fcompare_correct :
 forall f1 f2 : float,
 match Fcompare radix f1 f2 with
 | Datatypes.Eq => f1 = f2 :>R
 | Datatypes.Gt => (f1 < f2)%R
 | Datatypes.Lt => (f2 < f1)%R
 end.
intros f1 f2; generalize (Feq_bool_correct_t _ radixMoreThanOne f1 f2);
 generalize (Flt_bool_correct_t _ radixMoreThanOne f1 f2);
 generalize (Fle_bool_correct_f _ radixMoreThanOne f1 f2);
 unfold Flt_bool in |- *;
 unfold Flt_bool, Fle_bool, Feq_bool, Flt, Fle, Feq in |- *;
 case (Fcompare radix f1 f2); simpl in |- *; auto.
Qed.
 
Definition rClosestEvenPos (a : positive) (e : Z) :=
  match FindMin (vNum b) (Z2pos radix) a dExp e with
  | (r1, Float Z0 _) => rExact r1
  | (r1, r2) =>
      match
        Fcompare radix (Float 1%nat (Fexp r1))
          (Float (2%nat * Fnum r2) (Fexp r2))
      with
      | Datatypes.Gt => rRound (FSucc b radix precision r1)
      | Datatypes.Lt => rRound r1
      | Datatypes.Eq =>
          match ZevenP r1 with
          | true => rRound r1
          | false => rRound (FSucc b radix precision r1)
          end
      end
  end.
 
Definition rOp a :=
  match a with
  | rExact f => rExact (Fopp f)
  | rRound f => rRound (Fopp f)
  end.
 
Definition rClosestEven (f : float) :=
  match f with
  | Float Z0 e => rExact (Float 0 dExp)
  | Float (Zpos a) e => rClosestEvenPos a e
  | Float (Zneg a) e => rOp (rClosestEvenPos a e)
  end.
Opaque FindMin.
 
Theorem RleR0Rminus : forall x y, (x <= y)%R -> (0 <= y - x)%R.
intros x y; replace 0%R with (x - x)%R; auto with real.
unfold Rminus in |- *; auto with real.
Qed.
 
Theorem ClosestMin1 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (r - min <= max - r)%R -> Closest b radix r min.
intros r min max H H0 H1; (split; auto).
case H; auto.
intros f1 Hf1.
case (ClosestTotal b radix precision) with (r := r); auto with arith.
intros f2 Hf2; case (ClosestMinOrMax b radix) with (r := r) (p := f2);
 auto with arith.
intros H2.
replace (FtoR radix min) with (FtoRradix f2); auto.
case Hf2; auto.
apply (MinUniqueP b radix) with (r := r); auto with arith.
intros H2.
apply Rle_trans with (Rabs (FtoR radix f2 - r)).
2: case Hf2; auto.
replace (Rabs (FtoR radix min - r)) with (r - FtoRradix min)%R.
replace (Rabs (FtoR radix f2 - r)) with (FtoRradix max - r)%R; auto.
replace (FtoRradix max) with (FtoR radix f2).
apply sym_eq; apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H2; intros H3 (H4, H5); auto.
apply (MaxUniqueP b radix) with (r := r); auto with arith.
rewrite Rabs_minus_sym.
apply sym_eq; apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H; intros H3 (H4, H5); auto.
Qed.
 
Theorem ClosestMax1 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (max - r <= r - min)%R -> Closest b radix r max.
intros r min max H H0 H1; (split; auto).
case H0; auto.
intros f1 Hf1.
case (ClosestTotal b radix precision) with (r := r); auto with arith.
intros f2 Hf2; case (ClosestMinOrMax b radix) with (r := r) (p := f2);
 auto with arith.
intros H2.
apply Rle_trans with (Rabs (FtoR radix f2 - r)).
2: case Hf2; auto.
replace (Rabs (FtoR radix max - r)) with (FtoRradix max - r)%R.
replace (Rabs (FtoR radix f2 - r)) with (r - FtoRradix min)%R; auto.
replace (FtoRradix min) with (FtoR radix f2).
rewrite Rabs_minus_sym.
apply sym_eq; apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H2; intros H3 (H4, H5); auto.
apply (MinUniqueP b radix) with (r := r); auto with arith.
apply sym_eq; apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H0; intros H3 (H4, H5); auto.
intros H2.
replace (FtoR radix max) with (FtoRradix f2); auto.
case Hf2; auto.
apply (MaxUniqueP b radix) with (r := r); auto with arith.
Qed.
 
Theorem ClosestMin2 :
 forall (r : R) (min max f : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (r - min < max - r)%R -> Closest b radix r f -> f = min :>R.
intros r min max f H H0 H1 H2.
case (ClosestMinOrMax b radix) with (r := r) (p := f); auto with arith;
 intros H3.
apply (MinUniqueP b radix) with (r := r); auto with arith.
Contradict H1; apply Rle_not_lt.
replace (FtoRradix max - r)%R with (Rabs (max - r)).
replace (r - FtoRradix min)%R with (Rabs (FtoRradix min - r)).
cut (Fbounded b min); [ intros Fmin | case H; auto ].
replace (FtoRradix max) with (FtoRradix f).
case H2; auto.
apply (MaxUniqueP b radix) with (r := r); auto with arith.
rewrite Rabs_minus_sym.
apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H; intros H4 (H5, H6); auto.
apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H0; intros H4 (H5, H6); auto.
Qed.
 
Theorem ClosestMax2 :
 forall (r : R) (min max f : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (max - r < r - min)%R -> Closest b radix r f -> f = max :>R.
intros r min max f H H0 H1 H2.
case (ClosestMinOrMax b radix) with (r := r) (p := f); auto with arith;
 intros H3.
cut (Fbounded b max); [ intros Fmax | case H0; auto ].
Contradict H1; apply Rle_not_lt.
replace (FtoRradix max - r)%R with (Rabs (max - r)).
replace (r - FtoRradix min)%R with (Rabs (f - r)).
case H2; auto.
rewrite Rabs_minus_sym.
replace (FtoRradix min) with (FtoRradix f).
apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H3; intros H4 (H5, H6); auto.
apply (MinUniqueP b radix) with (r := r); auto with arith.
apply Rabs_pos_eq; auto.
apply RleR0Rminus.
case H0; intros H4 (H5, H6); auto.
apply (MaxUniqueP b radix) with (r := r); auto with arith.
Qed.
 
Theorem EvenClosestMin1 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (r - min < max - r)%R -> EvenClosest b radix precision r min.
intros r min max H H0 H1; split.
apply ClosestMin1 with (2 := H0); auto with real.
right; intros q H2; apply ClosestMin2 with (3 := H1); auto.
Qed.
 
Theorem EvenClosestMax1 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (max - r < r - min)%R -> EvenClosest b radix precision r max.
intros r min max H H0 H1; split.
apply ClosestMax1 with (1 := H); auto with real.
right; intros q H2; apply ClosestMax2 with (3 := H1); auto.
Qed.
 
Theorem EvenClosestMin2 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (r - min)%R = (max - r)%R ->
 FNeven b radix precision min -> EvenClosest b radix precision r min.
intros r min max H H0 H1 H2; split; auto.
apply ClosestMin1 with (2 := H0); auto with real.
Qed.
 
Theorem EvenClosestMax2 :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (max - r)%R = (r - min)%R ->
 FNeven b radix precision max -> EvenClosest b radix precision r max.
intros r min max H H0 H1; split; auto.
apply ClosestMax1 with (1 := H); auto with real.
Qed.
 
Theorem EqSpeTwice :
 forall x y z, (2%nat * (x - y))%R = (z - y)%R -> (x - y)%R = (z - x)%R.
intros x y z H.
replace (x - y)%R with (2%nat * (x - y) - (x - y))%R;
 [ idtac | simpl in |- *; ring ].
rewrite H; ring.
Qed.
 
Theorem RltSpeTwice1 :
 forall x y z, (2%nat * (x - y) < z - y)%R -> (x - y < z - x)%R.
intros x y z H.
replace (x - y)%R with (2%nat * (x - y) - (x - y))%R;
 [ idtac | simpl in |- *; ring ].
replace (z - x)%R with (z - y - (x - y))%R;
 [ unfold Rminus in |- *; auto with real | ring ].
Qed.
 
Theorem RltSpeTwice2 :
 forall x y z, (z - y < 2%nat * (x - y))%R -> (z - x < x - y)%R.
intros x y z H.
replace (x - y)%R with (2%nat * (x - y) - (x - y))%R;
 [ idtac | simpl in |- *; ring ].
replace (z - x)%R with (z - y - (x - y))%R;
 [ unfold Rminus in |- *; auto with real | ring ].
Qed.
 
Theorem rClosestEvenPos_correct :
 forall (a : positive) (e : Z),
 EvenClosest b radix precision (Float (Zpos a) e)
   (rFloat (rClosestEvenPos a e)) /\
 match rClosestEvenPos a e with
 | rExact r => r = Float (Zpos a) e :>R
 | rRound r => r <> Float (Zpos a) e :>R /\ Fcanonic radix b r
 end.
intros a e; unfold rClosestEvenPos in |- *; generalize (FminOp_correct1 a e);
 generalize (FminOp_correct2 a e); generalize (FminOp_correct3 a e);
 generalize (FminOp_correct4 a e); generalize (FminOp_correct5 a e);
 generalize (FminOp_correct6 a e); generalize (FminOp_correct7 a e);
 simpl in |- *; case (FindMin (vNum b) (Z2pos radix) a dExp e); 
 simpl in |- *; auto.
intros f0 f1; case f1; simpl in |- *; auto.
intros a'; case a'; simpl in |- *; auto.
intros e' H1 H2 H3 H4 H5 H6 H7; split; auto.
replace (FtoRradix (Float (Zpos a) e)) with (FtoRradix f0);
 auto with float arith.
unfold FtoRradix in |- *;
 apply
  RoundedModeProjectorIdem with (b := b) (P := EvenClosest b radix precision).
apply EvenClosestRoundedModeP; auto with arith.
case H1; simpl in |- *; auto.
rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
intros a'' e' H1 H2 H3 H4 H5 H6 H7.
cut (FtoRradix (Float (Zpos a'') e') <> 0%R :>R); [ intros NR1 | idtac ].
cut (Float (Zpos a) e <> f0 :>R); [ intros NR | idtac ].
case H4; clear H4; intros H4; [ Contradict NR1; auto | idtac ].
case H3; clear H3; intros H3; [ Contradict NR1; auto | idtac ].
generalize (Fcompare_correct (Float 1 (Fexp f0)) (Float (Zpos (xO a'')) e'));
 case (Fcompare radix (Float 1 (Fexp f0)) (Float (Zpos (xO a'')) e')).
generalize (ZevenP_correct f0); case (ZevenP f0); auto.
intros H8 H9; split; [ idtac | split ]; auto.
simpl in |- *;
 apply EvenClosestMin2 with (max := FNSucc b radix precision f0); 
 auto.
apply MinMax; auto; auto with arith.
apply EqSpeTwice; auto.
apply sym_eq.
replace (2%nat * (FtoRradix (Float (Zpos a) e) - FtoRradix f0))%R with
 (FtoRradix (Float 1 (Fexp f0))).
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FNSuccUlpPos; auto.
unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H9; rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (INR (nat_of_P (xO a''))) with (nat_of_P a'' + nat_of_P a'')%R.
ring.
rewrite <- plus_INR; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6;
 auto.
unfold FNeven in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
intros H8 H9; split; [ idtac | split ]; auto.
simpl in |- *; apply EvenClosestMax2 with (min := f0); auto.
rewrite <-
 (FcanonicFormalizeEq _ radixMoreThanOne b precision)
  with (p := f0); auto with arith.
change
  (isMax b radix (FtoRradix (Float (Zpos a) e)) (FNSucc b radix precision f0))
 in |- *; apply MinMax; auto with arith.
apply sym_eq; apply EqSpeTwice; auto.
apply sym_eq.
replace (2%nat * (FtoRradix (Float (Zpos a) e) - FtoRradix f0))%R with
 (FtoRradix (Float 1 (Fexp f0))).
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FSuccUlpPos; auto.
unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H9; rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (INR (nat_of_P (xO a''))) with (nat_of_P a'' + nat_of_P a'')%R.
ring.
rewrite <- plus_INR; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6;
 auto.
rewrite <-
 (FcanonicFormalizeEq _ radixMoreThanOne b precision)
  with (p := f0); auto with arith.
change (FNeven b radix precision (FNSucc b radix precision f0)) in |- *;
 apply FNoddSuc; auto with arith.
unfold FNodd in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
apply Rgt_not_eq.
red in |- *; rewrite H7.
replace (FtoRradix (FSucc b radix precision f0)) with
 (FtoRradix f0 + (FSucc b radix precision f0 - FtoRradix f0))%R.
apply Rplus_lt_compat_l.
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FSuccUlpPos; auto.
ring.
auto with float arith.
intros H8; split; [ idtac | split ]; auto.
simpl in |- *;
 apply EvenClosestMin1 with (max := FNSucc b radix precision f0);
 auto with float arith.
apply RltSpeTwice1.
replace (2%nat * (FtoRradix (Float (Zpos a) e) - FtoRradix f0))%R with
 (FtoRradix (Float (Zpos (xO a'')) e')).
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FNSuccUlpPos; auto.
unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
replace (powerRZ radix (Fexp f0)) with (FtoRradix (Float 1 (Fexp f0))); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (INR (nat_of_P (xO a''))) with (nat_of_P a'' + nat_of_P a'')%R.
ring.
rewrite <- plus_INR; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6;
 auto.
intros H8; split; [ idtac | split ]; auto.
simpl in |- *; apply EvenClosestMax1 with (min := f0); auto with float arith.
rewrite <-
 (FcanonicFormalizeEq _ radixMoreThanOne b precision)
  with (p := f0); auto with arith.
change
  (isMax b radix (FtoRradix (Float (Zpos a) e)) (FNSucc b radix precision f0))
 in |- *; apply MinMax; auto with arith.
apply RltSpeTwice2.
replace (2%nat * (FtoRradix (Float (Zpos a) e) - FtoRradix f0))%R with
 (FtoRradix (Float (Zpos (xO a'')) e')).
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FSuccUlpPos; auto.
unfold Fulp in |- *.
rewrite FcanonicFormalizeEq; auto with arith.
replace (powerRZ radix (Fexp f0)) with (FtoRradix (Float 1 (Fexp f0))); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite H7; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (INR (nat_of_P (xO a''))) with (nat_of_P a'' + nat_of_P a'')%R.
ring.
rewrite <- plus_INR; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6;
 auto.
apply Rgt_not_eq.
red in |- *; rewrite H7.
replace (FtoRradix (FSucc b radix precision f0)) with
 (FtoRradix f0 + (FSucc b radix precision f0 - FtoRradix f0))%R.
apply Rplus_lt_compat_l.
rewrite <- (Fminus_correct radix); auto with arith.
rewrite FSuccUlpPos; auto.
ring.
auto with float arith.
Contradict NR1; replace 0%R with (Float (Zpos a) e - Float (Zpos a) e)%R;
 [ idtac | ring ].
pattern (Float (Zpos a) e) at 2 in |- *; rewrite H7; rewrite NR1; ring.
apply NotR0NotZero; simpl in |- *; red in |- *; intros; discriminate.
intros p Fexp H H0 H1 H2 H3 H4; Contradict H4.
apply Rlt_not_le.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace 0%R with (-0 * powerRZ radix Fexp)%R; auto with real arith.
Qed.
 
Theorem rClosestEven_correct :
 forall f : float,
 EvenClosest b radix precision f (rFloat (rClosestEven f)) /\
 match rClosestEven f with
 | rExact r => r = f :>R
 | rRound r => r <> f :>R /\ Fcanonic radix b r
 end.
intros f; case f; intros a e; case a; simpl in |- *.
split; auto.
replace (FtoRradix (Float 0 e)) with (FtoRradix (Float 0 dExp)).
unfold FtoRradix in |- *;
 apply
  RoundedModeProjectorIdem with (b := b) (P := EvenClosest b radix precision);
 auto with float arith.
repeat (split; simpl in |- *; auto with zarith).
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
intros p; simpl in |- *; apply rClosestEvenPos_correct.
intros p; generalize (rClosestEvenPos_correct p e);
 case (rClosestEvenPos p e); simpl in |- *; auto.
intros f1 (H1, H2); replace (Float (Zneg p) e) with (Fopp (Float (Zpos p) e));
 try repeat rewrite (Fopp_correct radix); split; auto with real.
apply (EvenClosestSymmetric b radix precision); auto with arith.
intros f1 (H1, (H2, H3));
 replace (Float (Zneg p) e) with (Fopp (Float (Zpos p) e));
 try repeat rewrite (Fopp_correct radix); split; [ idtac | split ];
 auto with real float.
apply (EvenClosestSymmetric b radix precision); auto with arith.
assert
 (FtoR radix f1 <> FtoR radix (Float (Zpos p) e) ->
  (- FtoR radix f1)%R <> (- FtoR radix (Float (Zpos p) e))%R).
intro; red in |- *; intro; elim H;
 rewrite <- (Ropp_involutive (FtoR radix f1));
 rewrite <- (Ropp_involutive (FtoR radix (Float (Zpos p) e)));
 apply Ropp_eq_compat; assumption.
apply H; auto with real.
Qed.
End FminOp.
Transparent Pdiv.
Transparent PdivBound.
Transparent FindMin.