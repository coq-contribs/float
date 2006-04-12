(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export FroundProp.
Require Export Closest.
Section Fclosestp.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Coercion Local FtoRradix := FtoR radix.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem ClosestOpp :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (- r) (Fopp p).
intros p r H'; split.
apply oppBounded; auto.
case H'; auto.
intros f H'0.
rewrite Fopp_correct.
replace (- FtoR radix p - - r)%R with (- (FtoR radix p - r))%R;
 [ idtac | ring ].
replace (FtoR radix f - - r)%R with (- (- FtoR radix f - r))%R;
 [ idtac | ring ].
rewrite <- Fopp_correct.
repeat rewrite Rabs_Ropp.
case H'; auto with float.
Qed.
 
Theorem ClosestFabs :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (Rabs r) (Fabs p).
intros p r H'; case (Rle_or_lt 0 r); intros Rl0.
rewrite Rabs_right; auto with real.
replace (Fabs p) with p; auto.
unfold Fabs in |- *; apply floatEq; simpl in |- *; auto.
cut (0 <= Fnum p)%Z.
case (Fnum p); simpl in |- *; auto; intros p' H0; Contradict H0;
 apply Zlt_not_le; red in |- *; simpl in |- *; auto with zarith.
apply LeR0Fnum with (radix := radix); auto.
apply
 RleRoundedR0
  with (b := b) (precision := precision) (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto with real.
rewrite Faux.Rabsolu_left1; auto.
replace (Fabs p) with (Fopp p).
apply ClosestOpp; auto.
unfold Fabs in |- *; apply floatEq; simpl in |- *; auto.
cut (Fnum p <= 0)%Z.
case (Fnum p); simpl in |- *; auto; intros p' H0; Contradict H0;
 apply Zlt_not_le; red in |- *; simpl in |- *; auto with zarith.
apply R0LeFnum with (radix := radix); auto.
apply
 RleRoundedLessR0
  with (b := b) (precision := precision) (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
apply Rlt_le; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ClosestUlp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2%nat * Rabs (p - q) <= Fulp b radix precision q)%R.
intros p q H'.
case (Req_dec p q); intros Eqpq.
rewrite Eqpq.
replace (Rabs (q - q)) with 0%R;
 [ rewrite Rmult_0_r
 | replace (q - q)%R with 0%R; try ring; rewrite Rabs_right; auto with real ].
unfold Fulp in |- *; apply Rlt_le; auto with real arith.
replace (2%nat * Rabs (p - q))%R with (Rabs (p - q) + Rabs (p - q))%R;
 [ idtac | simpl in |- *; ring ].
case ClosestMinOrMax with (1 := H'); intros H'1.
apply Rle_trans with (Rabs (p - q) + Rabs (FNSucc b radix precision q - p))%R.
apply Rplus_le_compat_l.
rewrite <- (Rabs_Ropp (p - q)).
rewrite Ropp_minus_distr.
elim H'; auto.
intros H'0 H'2; apply H'2; auto.
apply FcanonicBound with (radix := radix); auto with float arith.
rewrite Rabs_right.
rewrite Rabs_right.
replace (p - q + (FNSucc b radix precision q - p))%R with
 (FNSucc b radix precision q - q)%R; [ idtac | ring ].
unfold FtoRradix in |- *; apply FulpSuc; auto.
case H'1; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
case MinMax with (3 := pGivesBound) (r := p) (p := q); auto with arith.
intros H'0 H'2; elim H'2; intros H'3 H'4; apply H'3; clear H'2; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
apply isMin_inv1 with (1 := H'1).
apply Rle_trans with (Rabs (p - q) + Rabs (p - FNPred b radix precision q))%R.
apply Rplus_le_compat_l.
rewrite <- (Rabs_Ropp (p - q));
 rewrite <- (Rabs_Ropp (p - FNPred b radix precision q)).
repeat rewrite Ropp_minus_distr.
elim H'; auto.
intros H'0 H'2; apply H'2; auto.
apply FcanonicBound with (radix := radix); auto with float arith.
rewrite <- (Rabs_Ropp (p - q)); rewrite Ropp_minus_distr.
rewrite Rabs_right.
rewrite Rabs_right.
replace (q - p + (p - FNPred b radix precision q))%R with
 (q - FNPred b radix precision q)%R; [ idtac | ring ].
unfold FtoRradix in |- *; apply FulpPred; auto.
case H'1; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
case MaxMin with (3 := pGivesBound) (r := p) (p := q); auto with arith.
intros H'0 H'2; elim H'2; intros H'3 H'4; apply H'3; clear H'2; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
apply isMax_inv1 with (1 := H'1).
Qed.
 
Theorem ClosestExp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2%nat * Rabs (p - q) <= powerRZ radix (Fexp q))%R.
intros p q H'.
apply Rle_trans with (Fulp b radix precision q).
apply (ClosestUlp p q); auto.
replace (powerRZ radix (Fexp q)) with (FtoRradix (Float 1%nat (Fexp q))).
apply (FulpLe b radix); auto.
apply
 RoundedModeBounded with (radix := radix) (P := Closest b radix) (r := p);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
ring.
Qed.
 
Theorem ClosestErrorExpStrict :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> q <> 0%R :>R -> (Fexp q < Fexp p)%Z.
intros.
case (Zle_or_lt (Fexp p) (Fexp q)); auto; intros Z1.
absurd (powerRZ radix (Fexp p) <= powerRZ radix (Fexp q))%R.
2: apply Rle_powerRZ; auto with real arith.
apply Rgt_not_le.
red in |- *; apply Rlt_le_trans with (2%nat * powerRZ radix (Fexp q))%R.
apply Rltdouble; auto with real arith.
apply Rle_trans with (2%nat * Fabs q)%R.
apply Rmult_le_compat_l; auto with real arith.
replace 0%R with (INR 0); auto with real arith.
replace (powerRZ radix (Fexp q)) with (FtoRradix (Float 1%nat (Fexp q)));
 auto.
apply (Fop.RleFexpFabs radix); auto with real zarith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite (Fabs_correct radix); auto with arith.
replace (FtoR radix q) with (x - p)%R; auto.
apply ClosestExp; auto.
Qed.
 
Theorem ClosestIdem :
 forall p q : float, Fbounded b p -> Closest b radix p q -> p = q :>R.
intros p q H' H'0.
case (Rabs_pos (q - p)); intros H1.
Contradict H1; apply Rle_not_lt.
replace 0%R with (Rabs (p - p)); [ case H'0; auto | idtac ].
replace (p - p)%R with 0%R; [ apply Rabs_R0; auto | ring ].
apply Rplus_eq_reg_l with (r := (- p)%R).
apply trans_eq with 0%R; [ ring | idtac ].
apply trans_eq with (q - p)%R; [ idtac | ring ].
generalize H1; unfold Rabs in |- *; case (Rcase_abs (q - p)); auto.
intros r H0; replace 0%R with (-0)%R; [ rewrite H0 | idtac ]; ring.
Qed.
 
Theorem ClosestM1 :
 forall (r1 r2 : R) (min max p q : float),
 isMin b radix r1 min ->
 isMax b radix r1 max ->
 (min + max < 2%nat * r2)%R ->
 Closest b radix r1 p -> Closest b radix r2 q -> (p <= q)%R.
intros r1 r2 min max p q H' H'0 H'1 H'2 H'3.
case (Rle_or_lt r2 max); intros H'4.
2: apply (ClosestMonotone b radix) with (p := r1) (q := r2); auto.
2: apply Rle_lt_trans with (FtoRradix max); auto.
2: apply isMax_inv1 with (1 := H'0).
case H'4; clear H'4; intros H'4.
2: replace (FtoRradix q) with (FtoRradix max).
2: case ClosestMinOrMax with (1 := H'2); intros H'5.
2: replace (FtoRradix p) with (FtoRradix min).
2: apply Rle_trans with r1.
2: apply isMin_inv1 with (1 := H').
2: apply isMax_inv1 with (1 := H'0).
2: apply MinEq with (1 := H'); auto.
2: replace (FtoRradix p) with (FtoRradix max); auto with real.
2: apply MaxEq with (1 := H'0); auto.
2: apply ClosestIdem; auto.
2: case H'0; auto.
2: rewrite <- H'4; auto.
cut (min < r2)%R.
2: apply Rmult_lt_reg_l with (r := INR 2); auto with real.
2: replace (2%nat * min)%R with (min + min)%R;
    [ idtac | simpl in |- *; ring ].
2: apply Rle_lt_trans with (2 := H'1).
2: apply Rplus_le_compat_l; auto with real.
2: apply Rle_trans with r1.
2: apply isMin_inv1 with (1 := H').
2: apply isMax_inv1 with (1 := H'0).
intros H'5.
replace (FtoRradix q) with (FtoRradix max).
case ClosestMinOrMax with (1 := H'2); intros H'6.
replace (FtoRradix p) with (FtoRradix min).
apply Rle_trans with r1.
apply isMin_inv1 with (1 := H').
apply isMax_inv1 with (1 := H'0).
apply MinEq with (1 := H'); auto.
replace (FtoRradix p) with (FtoRradix max); auto with real.
apply MaxEq with (1 := H'0); auto.
apply sym_eq.
apply (ClosestMaxEq b radix) with (r := r2) (min := min); auto.
apply isMinComp with (2 := H'0); auto.
apply isMaxComp with (1 := H'); auto.
Qed.
 
Theorem FmultRadixInv :
 forall (x z : float) (y : R),
 Fbounded b x ->
 Closest b radix y z -> (/ 2%nat * x < y)%R -> (/ 2%nat * x <= z)%R.
intros x z y H' H'0 H'1.
case MinEx with (r := (/ 2%nat * x)%R) (3 := pGivesBound); auto with arith.
intros min isMin.
case MaxEx with (r := (/ 2%nat * x)%R) (3 := pGivesBound); auto with arith.
intros max isMax.
case (Rle_or_lt y max); intros Rl1.
case Rl1; clear Rl1; intros Rl1.
replace (FtoRradix z) with (FtoRradix max).
apply isMax_inv1 with (1 := isMax).
apply sym_eq.
unfold FtoRradix in |- *;
 apply ClosestMaxEq with (b := b) (r := y) (min := min); 
 auto.
apply isMinComp with (r1 := (/ 2%nat * x)%R) (max := max); auto.
apply Rle_lt_trans with (2 := H'1); auto.
apply isMin_inv1 with (1 := isMin).
apply isMaxComp with (r1 := (/ 2%nat * x)%R) (min := min); auto.
apply Rle_lt_trans with (2 := H'1); auto.
apply isMin_inv1 with (1 := isMin).
replace (FtoR radix min + FtoR radix max)%R with (FtoRradix x).
apply Rmult_lt_reg_l with (r := (/ 2%nat)%R); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; try rewrite Rmult_1_l; auto with real.
unfold FtoRradix in |- *; apply (div2IsBetween b radix precision); auto.
cut (Closest b radix max z); [ intros C0 | idtac ].
replace (FtoRradix z) with (FtoRradix max); auto.
rewrite <- Rl1; auto.
apply Rlt_le; auto.
apply ClosestIdem; auto.
case isMax; auto.
apply (ClosestCompatible b radix y max z z); auto.
case H'0; auto.
apply Rle_trans with (FtoRradix max); auto.
apply isMax_inv1 with (1 := isMax).
apply (ClosestMonotone b radix (FtoRradix max) y); auto.
apply (RoundedModeProjectorIdem b radix (Closest b radix)); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
case isMax; auto.
Qed.
 
Theorem ClosestErrorBound :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> (Rabs q <= Float 1%nat (Fexp p) * / 2%nat)%R.
intros p q x H H0 H1.
apply Rle_trans with (Fulp b radix precision p * / 2%nat)%R.
rewrite H1.
replace (Rabs (x - p)) with (2%nat * Rabs (x - p) * / 2%nat)%R;
 [ idtac | ring ].
apply Rmult_le_compat_r; auto with real.
apply ClosestUlp; auto.
replace (/ 2%nat * (Rabs (x - p) * 2%nat))%R with
 (Rabs (x - p) * (2%nat * / 2%nat))%R.
replace (2%nat * / 2%nat)%R with 1%R.
ring.
apply sym_eq; apply Rinv_r; auto with real.
simpl in |- *; ring.
apply Rmult_le_compat_r.
apply Rlt_le.
apply Rinv_0_lt_compat; auto with real.
unfold FtoRradix in |- *; apply FulpLe; auto.
Qed.
 
Theorem ClosestErrorExp :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix x p ->
 q = (x - p)%R :>R ->
 exists error : float,
   Fbounded b error /\
   error = q :>R /\ (Fexp error <= Zmax (Fexp p - precision) (- dExp b))%Z.
intros p q x H H0 H1 H2; exists (Fnormalize radix b precision q).
cut (Fcanonic radix b (Fnormalize radix b precision q));
 [ intros C1 | apply FnormalizeCanonic; auto with arith ].
split.
apply FcanonicBound with (radix := radix); auto.
split.
apply (FnormalizeCorrect radix); auto.
case C1; intros C2.
apply Zle_trans with (Fexp p - precision)%Z; auto with zarith.
apply Zplus_le_reg_l with (Z_of_nat precision).
replace (precision + (Fexp p - precision))%Z with (Fexp p); [ idtac | ring ].
replace (precision + Fexp (Fnormalize radix b precision q))%Z with
 (Zsucc (Zpred precision + Fexp (Fnormalize radix b precision q)));
 [ idtac | unfold Zpred, Zsucc in |- *; ring ].
apply Zlt_le_succ.
apply Zlt_powerRZ with (IZR radix); auto with real zarith.
rewrite powerRZ_add; auto with real zarith.
apply
 Rle_lt_trans
  with
    (Zabs (Fnum (Fnormalize radix b precision q)) *
     powerRZ radix (Fexp (Fnormalize radix b precision q)))%R.
apply Rmult_le_compat_r; auto with real zarith.
replace (Zpred precision) with
 (Z_of_nat (pred (digit radix (Fnum (Fnormalize radix b precision q))))).
rewrite <- Zpower_nat_powerRZ.
apply Rle_IZR; apply digitLess; auto with real zarith.
change (~ is_Fzero (Fnormalize radix b precision q)) in |- *;
 apply (FnormalNotZero radix b); auto with float.
change
  (Z_of_nat (pred (Fdigit radix (Fnormalize radix b precision q))) =
   Zpred precision) in |- *.
rewrite FnormalPrecision with (precision := precision) (4 := C2);
 auto with zarith arith.
apply inj_pred; auto with arith.
change (Fabs (Fnormalize radix b precision q) < powerRZ radix (Fexp p))%R
 in |- *.
rewrite (Fabs_correct radix); auto; rewrite (FnormalizeCorrect radix); auto.
apply Rle_lt_trans with (Float 1%nat (Fexp p) * / 2%nat)%R.
apply ClosestErrorBound with (x := x); auto.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
pattern (powerRZ radix (Fexp p)) at 2 in |- *;
 replace (powerRZ radix (Fexp p)) with (powerRZ radix (Fexp p) * 1)%R;
 [ idtac | ring ].
replace (1 * powerRZ radix (Fexp p))%R with (powerRZ radix (Fexp p));
 [ apply Rmult_lt_compat_l | ring ].
apply powerRZ_lt; auto with arith real.
pattern 1%R at 3 in |- *; replace 1%R with (/ 1)%R.
apply Rinv_1_lt_contravar; auto with real.
replace 2%R with (INR 2); auto with real arith.
apply Zle_trans with (- dExp b)%Z; auto with float zarith.
case C2.
intros H3 H4; rewrite H3; auto with zarith.
Qed.
 
Theorem ClosestErrorBound2 :
 forall (x : R) (p : float),
 Closest b radix x p ->
 (Rabs (x - p) <=
  Rmax (Rabs p * (/ 2%nat * (radix * / Zpos (vNum b))))
    (/ 2%nat * powerRZ radix (- dExp b)))%R.
intros x p H.
apply Rle_trans with (/ 2%nat * Fulp b radix precision p)%R.
replace (Rabs (x - FtoRradix p)) with
 (/ 2%nat * (2%nat * Rabs (x - FtoRradix p)))%R.
apply Rmult_le_compat_l; auto with real.
apply ClosestUlp; auto.
rewrite <- Rmult_assoc; rewrite Rinv_l; simpl in |- *; auto with real.
cut (Fcanonic radix b (Fnormalize radix b precision p));
 [ intros tmp; Casec tmp; intros Fs | idtac ].
3: apply FnormalizeCanonic; auto with arith.
3: apply
    RoundedModeBounded with (radix := radix) (P := Closest b radix) (r := x);
    auto.
3: apply ClosestRoundedModeP with (precision := precision); auto.
2: elim Fs; intros H1 H2; elim H2; intros; clear H2.
2: unfold Fulp in |- *; rewrite H1; apply RmaxLess2.
apply Rle_trans with (Rabs p * (/ 2%nat * (radix * / Zpos (vNum b))))%R;
 [ idtac | apply RmaxLess1 ].
apply Rle_trans with (/ 2%nat * (Rabs p * (radix * / Zpos (vNum b))))%R;
 [ apply Rmult_le_compat_l | right; ring; ring ].
apply Rlt_le; apply Rinv_0_lt_compat; auto with real arith.
unfold Fulp in |- *.
replace (Fexp (Fnormalize radix b precision p)) with
 (Fexp (Fnormalize radix b precision p) + precision + - precision)%Z;
 [ idtac | ring ].
rewrite powerRZ_add; auto with real zarith.
apply Rle_trans with (Rabs p * radix * powerRZ radix (- precision))%R;
 [ apply Rmult_le_compat_r | right ]; auto with real zarith.
2: rewrite pGivesBound; simpl in |- *.
2: rewrite powerRZ_Zopp; auto with real zarith; rewrite Zpower_nat_powerRZ;
    auto with real zarith; ring.
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p));
 [ idtac | apply (FnormalizeCorrect radix) ]; auto.
rewrite <- (Fabs_correct radix); unfold FtoR in |- *; simpl in |- *;
 auto with arith.
rewrite powerRZ_add; auto with real zarith.
replace
 (Zabs (Fnum (Fnormalize radix b precision p)) *
  powerRZ radix (Fexp (Fnormalize radix b precision p)) * radix)%R with
 (powerRZ radix (Fexp (Fnormalize radix b precision p)) *
  (Zabs (Fnum (Fnormalize radix b precision p)) * radix))%R; 
 [ idtac | ring ].
apply Rmult_le_compat_l; auto with arith real.
rewrite <- Zpower_nat_powerRZ; auto with real zarith.
rewrite <- Rmult_IZR; apply Rle_IZR.
rewrite <- pGivesBound; pattern radix at 2 in |- *;
 rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult.
rewrite Zmult_comm; case Fs; auto.
Qed.
End Fclosestp.
Hint Resolve ClosestOpp ClosestFabs ClosestUlp: float.