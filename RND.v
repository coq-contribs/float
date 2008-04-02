Require Export ClosestMult.

Section Round.
Variable b : Fbound.
Variable radix : Z.
Variable p : nat.
 
Coercion Local FtoRradix := FtoR radix.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis pGreaterThanOne : 1 < p.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.


(** Various lemmas about exp, ln *)

Theorem exp_ln_powerRZ :
 forall u v : Z, (0 < u)%Z -> exp (ln u * v) = powerRZ u v.
intros u v H1.
cut (forall e f : nat, (0 < e)%Z -> exp (ln e * f) = powerRZ e f).
intros H2.
case (Zle_or_lt 0 v); intros H3.
replace u with (Z_of_nat (Zabs_nat u));
 [ idtac | apply inj_abs; auto with zarith ].
replace v with (Z_of_nat (Zabs_nat v)); [ idtac | apply inj_abs; auto ].
repeat rewrite <- INR_IZR_INZ; apply H2.
rewrite inj_abs; auto with zarith.
replace v with (- Zabs_nat v)%Z.
rewrite <- Rinv_powerRZ; auto with zarith real.
replace u with (Z_of_nat (Zabs_nat u));
 [ idtac | apply inj_abs; auto with zarith ].
rewrite Ropp_Ropp_IZR; rewrite Ropp_mult_distr_r_reverse; rewrite exp_Ropp;
 repeat rewrite <- INR_IZR_INZ.
rewrite H2; auto with real.
rewrite inj_abs; auto with zarith.
rewrite <- Zabs_absolu; rewrite <- Zabs_Zopp.
rewrite Zabs_eq; auto with zarith.
intros e f H2.
induction  f as [| f Hrecf].
simpl in |- *; ring_simplify (ln e * 0)%R; apply exp_0.
replace (ln e * S f)%R with (ln e * f + ln e)%R.
rewrite exp_plus; rewrite Hrecf; rewrite exp_ln; auto with real zarith.
replace (Z_of_nat (S f)) with (f + 1)%Z.
rewrite powerRZ_add; auto with real zarith.
rewrite inj_S; auto with zarith.
replace (INR (S f)) with (f + 1)%R; [ ring | idtac ].
apply trans_eq with (IZR (f + 1)).
rewrite plus_IZR; simpl in |- *; rewrite <- INR_IZR_INZ; auto with real.
apply trans_eq with (IZR (Zsucc f)); auto with zarith real.
rewrite <- inj_S; rewrite <- INR_IZR_INZ; auto with zarith real.
Qed.

Theorem ln_radix_pos : (0 < ln radix)%R.
rewrite <- ln_1.
apply ln_increasing; auto with real zarith.
Qed.

Theorem exp_le_inv : forall x y : R, (exp x <= exp y)%R -> (x <= y)%R.
intros x y H; case H; intros H2.
left; apply exp_lt_inv; auto.
right; apply exp_inv; auto.
Qed.

Theorem exp_monotone : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
intros x y H; case H; intros H2.
left; apply exp_increasing; auto.
right; auto with real.
Qed.

Theorem firstNormalPos_eq :
 FtoRradix (firstNormalPos radix b p) = powerRZ radix (Zpred p + - dExp b).
unfold firstNormalPos, nNormMin, FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Zpower_nat_Z_powerRZ; rewrite powerRZ_add; auto with real zarith.
replace (Z_of_nat (pred p)) with (Zpred p);
 [ ring | rewrite inj_pred; auto with zarith ].
Qed.


(** Results about the ineger rounding down *)

Definition IRNDD (r : R) := Zpred (up r).

Theorem IRNDD_correct1 : forall r : R, (IRNDD r <= r)%R. 
intros r; unfold IRNDD in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
unfold Zpred in |- *; apply Rplus_le_reg_l with (1 + - r)%R.
ring_simplify (1 + - r + r)%R.
apply Rle_trans with (2 := H2).
rewrite plus_IZR; right; simpl in |- *; ring.
Qed.

Theorem IRNDD_correct2 : forall r : R, (r < Zsucc (IRNDD r))%R.
intros r; unfold IRNDD in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
rewrite <- Zsucc_pred; auto.
Qed.

Theorem IRNDD_correct3 : forall r : R, (r - 1 < IRNDD r)%R.
intros r; unfold IRNDD in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
unfold Zpred, Rminus in |- *; rewrite plus_IZR; simpl in |- *; auto with real. 
Qed.

Hint Resolve IRNDD_correct1 IRNDD_correct2 IRNDD_correct3: real.


Theorem IRNDD_pos : forall r : R, (0 <= r)%R -> (0 <= IRNDD r)%R.
intros r H1; unfold IRNDD in |- *.
generalize (archimed r); intros T; elim T; intros H3 H2; clear T.
replace 0%R with (IZR 0); auto with real; apply IZR_le.
apply Zle_Zpred.
apply lt_IZR; apply Rle_lt_trans with r; auto with real zarith.
Qed.


Theorem IRNDD_monotone : forall r s : R, (r <= s)%R -> (IRNDD r <= IRNDD s)%R.
intros r s H.
apply Rle_IZR; apply Zgt_succ_le; apply Zlt_gt; apply lt_IZR.
apply Rle_lt_trans with r; auto with real.
apply Rle_lt_trans with s; auto with real.
Qed.


Theorem IRNDD_eq :
 forall (r : R) (z : Z), (z <= r)%R -> (r < Zsucc z)%R -> IRNDD r = z.
intros r z H1 H2.
cut (IRNDD r - z < 1)%Z;
 [ intros H3 | apply lt_IZR; rewrite <- Z_R_minus; simpl in |- * ].
cut (z - IRNDD r < 1)%Z;
 [ intros H4; auto with zarith
 | apply lt_IZR; rewrite <- Z_R_minus; simpl in |- * ].
unfold Rminus in |- *; apply Rle_lt_trans with (r + - IRNDD r)%R;
 auto with real.
apply Rlt_le_trans with (r + - (r - 1))%R; auto with real; right; ring.
unfold Rminus in |- *; apply Rle_lt_trans with (r + - z)%R; auto with real.
apply Rlt_le_trans with (Zsucc z + - z)%R; auto with real; right;
 unfold Zsucc in |- *; rewrite plus_IZR; simpl in |- *; 
 ring.
Qed.

Theorem IRNDD_projector : forall z : Z, IRNDD z = z.
intros z.
apply IRNDD_eq; auto with zarith real.
Qed.


(** Rounding down of a positive real *)

Definition RND_Min_Pos (r : R) :=
  match Rle_dec (firstNormalPos radix b p) r with
  | left _ =>
      let e := IRNDD (ln r / ln radix + (- Zpred p)%Z) in
      Float (IRNDD (r * powerRZ radix (- e))) e
  | right _ => Float (IRNDD (r * powerRZ radix (dExp b))) (- dExp b)
  end.


Theorem RND_Min_Pos_bounded_aux :
 forall (r : R) (e : Z),
 (0 <= r)%R ->
 (- dExp b <= e)%Z ->
 (r < powerRZ radix (e + p))%R ->
 Fbounded b (Float (IRNDD (r * powerRZ radix (- e))) e).
intros r e H1 H2 H3.
split; auto.
simpl in |- *; rewrite pGivesBound; apply lt_IZR.
rewrite Zpower_nat_Z_powerRZ; rewrite <- Faux.Rabsolu_Zabs.
rewrite Rabs_right;
 [ idtac
 | apply Rle_ge; apply IRNDD_pos; apply Rmult_le_pos; auto with real zarith ].
apply Rle_lt_trans with (1 := IRNDD_correct1 (r * powerRZ radix (- e))).
apply Rmult_lt_reg_l with (powerRZ radix e); auto with zarith real.
rewrite Rmult_comm; rewrite Rmult_assoc.
rewrite <- powerRZ_add; auto with zarith real.
rewrite <- powerRZ_add; auto with zarith real.
apply Rle_lt_trans with (2 := H3); ring_simplify (- e + e)%Z; simpl in |- *; right;
 ring.
Qed.


Theorem RND_Min_Pos_canonic :
 forall r : R, (0 <= r)%R -> Fcanonic radix b (RND_Min_Pos r).
intros r H1; unfold RND_Min_Pos in |- *.
generalize ln_radix_pos; intros W.
case (Rle_dec (firstNormalPos radix b p) r); intros H2.
cut (0 < r)%R; [ intros V | idtac ].
2: apply Rlt_le_trans with (2 := H2); rewrite firstNormalPos_eq;
    auto with real zarith.
left; split.
apply RND_Min_Pos_bounded_aux; auto.
apply Zgt_succ_le; apply Zlt_gt.
apply lt_IZR.
apply
 Rle_lt_trans with (2 := IRNDD_correct2 (ln r / ln radix + (- Zpred p)%Z)).
apply Rplus_le_reg_l with (Zpred p).
apply Rmult_le_reg_l with (ln radix).
apply ln_radix_pos.
apply Rle_trans with (ln r).
apply exp_le_inv.
rewrite exp_ln; auto.
replace (Zpred p + (- dExp b)%Z)%R with (IZR (Zpred p + - dExp b)).
rewrite exp_ln_powerRZ; auto with zarith.
apply Rle_trans with (2 := H2).
rewrite firstNormalPos_eq; auto with real.
rewrite plus_IZR; rewrite Ropp_Ropp_IZR; ring.
rewrite Ropp_Ropp_IZR; right; field; auto with real.
rewrite <- exp_ln_powerRZ; auto with zarith.
pattern r at 1 in |- *; rewrite <- (exp_ln r); auto.
apply exp_increasing.
rewrite plus_IZR.
apply
 Rle_lt_trans with (ln radix * (ln r / ln radix + (- Zpred p)%Z - 1 + p))%R.
rewrite Ropp_Ropp_IZR; unfold Zpred in |- *; rewrite plus_IZR; simpl in |- *.
repeat rewrite <- INR_IZR_INZ; right; field; auto with real.
apply Rmult_lt_compat_l; auto with real.
repeat rewrite <- INR_IZR_INZ.
apply Rplus_lt_compat_r; auto with real.
simpl in |- *; rewrite pGivesBound; apply le_IZR; simpl in |- *.
rewrite Zpower_nat_Z_powerRZ; rewrite Zabs_eq.
2: apply le_IZR; rewrite Rmult_IZR; simpl in |- *.
2: apply Rmult_le_pos; auto with real zarith; apply IRNDD_pos;
    apply Rmult_le_pos; auto with real zarith.
rewrite Rmult_IZR; pattern (Z_of_nat p) at 1 in |- *;
 replace (Z_of_nat p) with (1 + Zpred p)%Z.
2: unfold Zpred in |- *; ring.
rewrite powerRZ_add; auto with zarith real; simpl in |- *; ring_simplify (radix * 1)%R.
apply Rmult_le_compat_l; auto with zarith real.
rewrite <- inj_pred; auto with zarith.
rewrite <- Zpower_nat_Z_powerRZ; apply IZR_le.
apply Zgt_succ_le; apply Zlt_gt; apply lt_IZR; rewrite Ropp_Ropp_IZR.
apply
 Rle_lt_trans
  with (r * powerRZ radix (- IRNDD (ln r / ln radix + - pred p)))%R.
2: repeat rewrite <- INR_IZR_INZ; apply IRNDD_correct2.
rewrite <- exp_ln_powerRZ; auto with zarith.
rewrite Zpower_nat_Z_powerRZ; rewrite Ropp_Ropp_IZR.
apply Rle_trans with (r * exp (ln radix * - (ln r / ln radix + - pred p)))%R.
pattern r at 1 in |- *; rewrite <- (exp_ln r); auto; rewrite <- exp_plus.
replace (ln r + ln radix * - (ln r / ln radix + - pred p))%R with
 (ln radix * pred p)%R.
2: field; auto with real.
rewrite INR_IZR_INZ; rewrite exp_ln_powerRZ; auto with real zarith.
apply Rmult_le_compat_l; auto with real.
apply exp_monotone; auto with real.
cut (r < powerRZ radix (Zpred p + - dExp b))%R; [ intros H3 | idtac ].
2: rewrite <- firstNormalPos_eq; auto with real.
right; split.
pattern (dExp b) at 2 in |- *;
 replace (Z_of_N (dExp b)) with (- - dExp b)%Z; auto with zarith.
apply RND_Min_Pos_bounded_aux; auto with zarith.
apply Rlt_trans with (1 := H3); apply Rlt_powerRZ; auto with real zarith.
rewrite Zplus_comm; auto with zarith.
split; [ simpl in |- *; auto | idtac ].
simpl in |- *; rewrite pGivesBound; apply lt_IZR.
rewrite Zpower_nat_Z_powerRZ; rewrite <- Faux.Rabsolu_Zabs.
rewrite mult_IZR; rewrite Rabs_right;
 [ idtac
 | apply Rle_ge; apply Rmult_le_pos; auto with real zarith; apply IRNDD_pos;
    apply Rmult_le_pos; auto with real zarith ].
apply Rle_lt_trans with (radix * (r * powerRZ radix (dExp b)))%R;
 auto with real zarith.
apply
 Rlt_le_trans
  with
    (radix * (powerRZ radix (Zpred p + - dExp b) * powerRZ radix (dExp b)))%R;
 auto with real zarith.
rewrite <- powerRZ_add; auto with zarith real.
pattern (IZR radix) at 1 in |- *; replace (IZR radix) with (powerRZ radix 1);
 [ rewrite <- powerRZ_add | simpl in |- * ]; auto with zarith real;
 unfold Zpred in |- *.
ring_simplify (1 + (p + -1 + - dExp b + dExp b))%Z; auto with real.
Qed.

Theorem RND_Min_Pos_Rle : forall r : R, (0 <= r)%R -> (RND_Min_Pos r <= r)%R.
intros r H.
unfold RND_Min_Pos in |- *; case (Rle_dec (firstNormalPos radix b p) r);
 intros H2.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply
 Rle_trans
  with
    (r * powerRZ radix (- IRNDD (ln r / ln radix + (- Zpred p)%Z)) *
     powerRZ radix (IRNDD (ln r / ln radix + (- Zpred p)%Z)))%R;
 auto with real.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
ring_simplify
    (- IRNDD (ln r / ln radix + (- Zpred p)%Z) +
     IRNDD (ln r / ln radix + (- Zpred p)%Z))%Z; simpl in |- *;
 auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply
 Rle_trans with (r * powerRZ radix (dExp b) * powerRZ radix (- dExp b))%R;
 auto with real.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
ring_simplify (dExp b + - dExp b)%Z; simpl in |- *; auto with real.
Qed.



Theorem RND_Min_Pos_monotone :
 forall r s : R,
 (0 <= r)%R -> (r <= s)%R -> (RND_Min_Pos r <= RND_Min_Pos s)%R.
intros r s V1 H.
cut (0 <= s)%R;
 [ intros V2 | apply Rle_trans with (1 := V1); auto with real ].
rewrite <-
 FPredSuc
          with
          (x := RND_Min_Pos s)
         (precision := p)
         (b := b)
         (radix := radix); auto with arith.
2: apply RND_Min_Pos_canonic; auto.
unfold FtoRradix in |- *; apply FPredProp; auto with arith;
 fold FtoRradix in |- *.
apply RND_Min_Pos_canonic; auto.
apply FSuccCanonic; auto with arith; apply RND_Min_Pos_canonic; auto.
apply Rle_lt_trans with r; auto with real.
apply RND_Min_Pos_Rle; auto.
apply Rle_lt_trans with (1 := H).
replace (FtoRradix (FSucc b radix p (RND_Min_Pos s))) with
 (RND_Min_Pos s + powerRZ radix (Fexp (RND_Min_Pos s)))%R.
unfold RND_Min_Pos in |- *; case (Rle_dec (firstNormalPos radix b p) s);
 intros H1.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply
 Rle_lt_trans
  with
    ((s * powerRZ radix (- IRNDD (ln s / ln radix + (- Zpred p)%Z)) - 1) *
     powerRZ radix (IRNDD (ln s / ln radix + (- Zpred p)%Z)) +
     powerRZ radix (IRNDD (ln s / ln radix + (- Zpred p)%Z)))%R;
 auto with real.
right; ring_simplify.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with zarith real.
ring_simplify
    (-IRNDD (ln s / ln radix + (- Zpred p)%Z) +
      IRNDD (ln s / ln radix + (- Zpred p)%Z))%Z; 
   simpl; ring.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply
 Rle_lt_trans
  with
    ((s * powerRZ radix (dExp b) - 1) * powerRZ radix (- dExp b) +
     powerRZ radix (- dExp b))%R; auto with real.
right; ring_simplify.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with zarith real.
ring_simplify (dExp b + -dExp b)%Z; simpl in |- *; ring.
replace (powerRZ radix (Fexp (RND_Min_Pos s))) with
 (FtoR radix (Float 1%nat (Fexp (RND_Min_Pos s))));
 [ idtac | unfold FtoR in |- *; simpl in |- *; ring ].
rewrite <- FSuccDiff1 with b radix p (RND_Min_Pos s); auto with arith.
rewrite Fminus_correct; auto with zarith; fold FtoRradix in |- *; ring.
cut (- nNormMin radix p < Fnum (RND_Min_Pos s))%Z; auto with zarith.
apply Zlt_le_trans with 0%Z.
replace 0%Z with (- (0))%Z; unfold nNormMin in |- *; auto with arith zarith.
apply le_IZR; unfold RND_Min_Pos in |- *;
 case (Rle_dec (firstNormalPos radix b p) s); intros H1; 
 simpl in |- *; apply IRNDD_pos; apply Rmult_le_pos; 
 auto with real zarith.
Qed.


Theorem RND_Min_Pos_projector :
 forall f : float,
 (0 <= f)%R -> Fcanonic radix b f -> FtoRradix (RND_Min_Pos f) = f.
intros f H1 H2.
unfold RND_Min_Pos in |- *; case (Rle_dec (firstNormalPos radix b p) f);
 intros H3.
replace (IRNDD (ln f / ln radix + (- Zpred p)%Z)) with (Fexp f).
replace (f * powerRZ radix (- Fexp f))%R with (IZR (Fnum f)).
rewrite IRNDD_projector; unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
ring_simplify (Fexp f + - Fexp f)%Z; simpl in |- *; ring.
generalize ln_radix_pos; intros V1.
cut (0 < Fnum f)%R; [ intros V2 | idtac ].
apply sym_eq; apply IRNDD_eq.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite ln_mult; auto with real zarith.
unfold Rdiv in |- *; rewrite Rmult_plus_distr_r.
apply Rle_trans with (Zpred p + Fexp f + (- Zpred p)%Z)%R;
 [ rewrite Ropp_Ropp_IZR; right; ring | idtac ].
apply Rplus_le_compat_r; apply Rplus_le_compat.
apply Rmult_le_reg_l with (ln radix); [ auto with real | idtac ].
apply Rle_trans with (ln (Fnum f)); [ idtac | right; field; auto with real ].
apply exp_le_inv.
rewrite exp_ln; auto.
rewrite exp_ln_powerRZ; auto with zarith.
case H2; intros T; elim T; intros C1 C2.
apply Rmult_le_reg_l with radix; auto with real zarith.
apply Rle_trans with (IZR (Zpos (vNum b)));
 [ right; rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ | idtac ].
pattern (Z_of_nat p) at 2 in |- *; replace (Z_of_nat p) with (1 + Zpred p)%Z;
 [ rewrite powerRZ_add; auto with real zarith; simpl in |- *; ring
 | unfold Zpred in |- *; ring ].
rewrite <- (Rabs_right (radix * Fnum f)); auto with real zarith.
rewrite <- mult_IZR; rewrite Faux.Rabsolu_Zabs; auto with real zarith.
apply Rle_ge; apply Rmult_le_pos; auto with real zarith.
Contradict H3; apply Rlt_not_le; unfold FtoRradix in |- *;
 apply FsubnormalLtFirstNormalPos; auto with zarith.
apply Rmult_le_reg_l with (ln radix); [ auto with real | idtac ].
apply Rle_trans with (ln (powerRZ radix (Fexp f)));
 [ idtac | right; field; auto with real ].
rewrite <- exp_ln_powerRZ; auto with zarith.
rewrite ln_exp; auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite ln_mult; auto with real zarith.
rewrite <- exp_ln_powerRZ; auto with zarith.
rewrite ln_exp; auto with real.
unfold Rdiv in |- *; rewrite Rmult_plus_distr_r.
apply Rlt_le_trans with (p + Fexp f + (- Zpred p)%Z)%R.
2: rewrite Ropp_Ropp_IZR; unfold Zsucc, Zpred in |- *;
    repeat rewrite plus_IZR; repeat rewrite <- INR_IZR_INZ; 
    simpl in |- *; right; ring.
replace (ln radix * Fexp f * / ln radix)%R with (IZR (Fexp f));
 [ idtac | field; auto with real ].
apply Rplus_lt_compat_r; apply Rplus_lt_compat_r.
apply Rmult_lt_reg_l with (ln radix); [ auto with real | idtac ].
apply Rle_lt_trans with (ln (Fnum f));
 [ right; field; auto with real | idtac ].
apply exp_lt_inv.
rewrite exp_ln; auto.
rewrite INR_IZR_INZ; rewrite exp_ln_powerRZ; auto with zarith.
apply Rlt_le_trans with (IZR (Zpos (vNum b))).
rewrite <- (Rabs_right (IZR (Fnum f))); auto with real.
rewrite Faux.Rabsolu_Zabs; apply Rlt_IZR; cut (Fbounded b f);
 auto with real zarith float.
apply FcanonicBound with radix; auto.
apply Rle_ge; auto with real.
right; rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ; auto with real zarith.
replace 0%R with (IZR 0); auto with real zarith; apply Rlt_IZR.
apply LtR0Fnum with radix; auto with zarith; fold FtoRradix in |- *.
apply Rlt_le_trans with (2 := H3); rewrite firstNormalPos_eq;
 auto with real zarith.
case H2; intros T; elim T; intros C1 C2.
absurd (firstNormalPos radix b p <= f)%R; auto with real.
unfold FtoRradix in |- *; apply FnormalLtFirstNormalPos; auto with arith.
elim C2; intros C3 C4.
replace (f * powerRZ radix (dExp b))%R with (IZR (Fnum f)).
rewrite IRNDD_projector; rewrite <- C3; unfold FtoRradix, FtoR in |- *;
 simpl in |- *; ring.
unfold FtoRradix, FtoR in |- *; rewrite C3.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
ring_simplify (- dExp b + dExp b)%Z; simpl in |- *; ring.
Qed.

Theorem RND_Min_Pos_correct :
 forall r : R, (0 <= r)%R -> isMin b radix r (RND_Min_Pos r).
intros r H1.
split.
apply FcanonicBound with radix; apply RND_Min_Pos_canonic; auto.
split.
apply RND_Min_Pos_Rle; auto.
fold FtoRradix in |- *; intros f H2 H3.
case (Rle_or_lt 0 f); intros H4.
unfold FtoRradix in |- *; rewrite <- FnormalizeCorrect with radix b p f; auto;
 fold FtoRradix in |- *.
rewrite <- RND_Min_Pos_projector.
apply RND_Min_Pos_monotone; unfold FtoRradix in |- *;
 rewrite FnormalizeCorrect; auto.
unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto.
apply FnormalizeCanonic; auto with arith.
apply Rle_trans with 0%R; auto with real.
unfold RND_Min_Pos in |- *; case (Rle_dec (firstNormalPos radix b p) r);
 intros H5; unfold FtoRradix, FtoR in |- *; simpl in |- *; 
 apply Rmult_le_pos; auto with real zarith; apply IRNDD_pos;
 apply Rmult_le_pos; auto with real zarith.
Qed.


(** Easily deduced, the rounding up of a positive real *)

Definition RND_Max_Pos (r : R) :=
  match Req_EM_T r (RND_Min_Pos r) with
  | left _ => RND_Min_Pos r
  | right _ => FSucc b radix p (RND_Min_Pos r)
  end.

Theorem RND_Max_Pos_canonic :
 forall r : R, (0 <= r)%R -> Fcanonic radix b (RND_Max_Pos r).
intros r H; unfold RND_Max_Pos in |- *.
case (Req_EM_T r (RND_Min_Pos r)); intros H1.
apply RND_Min_Pos_canonic; auto.
apply FSuccCanonic; auto with arith; apply RND_Min_Pos_canonic; auto.
Qed.

Theorem RND_Max_Pos_Rle : forall r : R, (0 <= r)%R -> (r <= RND_Max_Pos r)%R.
intros r H.
unfold RND_Max_Pos in |- *; case (Req_EM_T r (RND_Min_Pos r)); intros H1.
rewrite <- H1; auto with real.
case (Rle_or_lt r (FSucc b radix p (RND_Min_Pos r))); auto; intros H2.
generalize (RND_Min_Pos_correct r H); intros T; elim T; intros H3 T1; elim T1;
 intros H4 H5; clear T T1.
absurd (FSucc b radix p (RND_Min_Pos r) <= RND_Min_Pos r)%R;
 auto with float zarith real.
apply Rlt_not_le; auto with float zarith.
unfold FtoRradix in |- *; apply FSuccLt; auto with arith.
Qed.

Theorem RND_Max_Pos_correct :
 forall r : R, (0 <= r)%R -> isMax b radix r (RND_Max_Pos r).
intros r H.
split.
apply FcanonicBound with radix; apply RND_Max_Pos_canonic; auto.
split.
apply RND_Max_Pos_Rle; auto.
unfold RND_Max_Pos in |- *; case (Req_EM_T r (RND_Min_Pos r)); intros H1.
fold FtoRradix in |- *; intros f H2 H3; rewrite <- H1; auto with real.
fold FtoRradix in |- *; intros f H2 H3.
case H3; intros V.
case (Rle_or_lt (FSucc b radix p (RND_Min_Pos r)) f); auto; intros H4.
absurd (f < f)%R; auto with real.
apply Rle_lt_trans with (RND_Min_Pos r).
rewrite <- FPredSuc with b radix p (RND_Min_Pos r); auto with arith.
2: apply RND_Min_Pos_canonic; auto.
unfold FtoRradix in |- *; rewrite <- FnormalizeCorrect with radix b p f; auto.
apply FPredProp; auto with arith float zarith.
apply FSuccCanonic; auto with arith; apply RND_Min_Pos_canonic; auto.
rewrite FnormalizeCorrect; auto with real.
apply Rle_lt_trans with (2 := V).
apply RND_Min_Pos_Rle; auto.
Contradict H1.
rewrite V; unfold FtoRradix in |- *;
 rewrite <- FnormalizeCorrect with radix b p f; auto.
fold FtoRradix in |- *; apply sym_eq; apply RND_Min_Pos_projector;
 auto with zarith float.
unfold FtoRradix in |- *; rewrite FnormalizeCorrect; fold FtoRradix in |- *;
 auto with real.
apply Rle_trans with r; auto with real.
Qed.

(** Roundings up and down of any real *)

Definition RND_Min (r : R) :=
  match Rle_dec 0 r with
  | left _ => RND_Min_Pos r
  | right _ => Fopp (RND_Max_Pos (- r))
  end.

Theorem RND_Min_canonic : forall r : R, Fcanonic radix b (RND_Min r).
intros r.
unfold RND_Min in |- *; case (Rle_dec 0 r); intros H.
apply RND_Min_Pos_canonic; auto.
apply FcanonicFopp; apply RND_Max_Pos_canonic; auto with real.
Qed.

Theorem RND_Min_correct : forall r : R, isMin b radix r (RND_Min r).
intros r.
unfold RND_Min in |- *; case (Rle_dec 0 r); intros H.
apply RND_Min_Pos_correct; auto.
pattern r at 1 in |- *; rewrite <- (Ropp_involutive r).
apply MaxOppMin; apply RND_Max_Pos_correct; auto with real.
Qed.

Definition RND_Max (r : R) :=
  match Rle_dec 0 r with
  | left _ => RND_Max_Pos r
  | right _ => Fopp (RND_Min_Pos (- r))
  end.

Theorem RND_Max_canonic : forall r : R, Fcanonic radix b (RND_Max r).
intros r.
unfold RND_Max in |- *; case (Rle_dec 0 r); intros H.
apply RND_Max_Pos_canonic; auto.
apply FcanonicFopp; apply RND_Min_Pos_canonic; auto with real.
Qed.

Theorem RND_Max_correct : forall r : R, isMax b radix r (RND_Max r).
intros r.
unfold RND_Max in |- *; case (Rle_dec 0 r); intros H.
apply RND_Max_Pos_correct; auto.
pattern r at 1 in |- *; rewrite <- (Ropp_involutive r).
apply MinOppMax; apply RND_Min_Pos_correct; auto with real.
Qed.

Definition RND_Zero (r : R) :=
  match Rle_dec 0 r with
  | left _ =>  RND_Min r
  | right _ => RND_Max r
  end.

Theorem RND_Zero_canonic : forall r : R, Fcanonic radix b (RND_Zero r).
intros r.
unfold RND_Zero in |- *; case (Rle_dec 0 r); intros H.
apply RND_Min_canonic; auto.
apply RND_Max_canonic; auto.
Qed.

Theorem RND_Zero_correct : forall r : R, ToZeroP b radix r (RND_Zero r).
intros r.
unfold ToZeroP, RND_Zero.
case (Rle_dec 0 r); intros H.
left; split; auto with real; apply RND_Min_correct; auto with real.
right; split; auto with real;apply RND_Max_correct; auto with real.
Qed.


(** Rounding to the nearest of any real 
    First, ClosestUp  (when equality, the biggest is returned)
    Then, EvenClosest (when equality, the even is returned)
*)

Definition RND_ClosestUp (r : R) :=
  match Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) with
  | left _ => RND_Max r
  | right _ => RND_Min r
  end.


Theorem RND_ClosestUp_canonic :
 forall r : R, Fcanonic radix b (RND_ClosestUp r).
intros r.
unfold RND_ClosestUp in |- *;
 case (Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r))); 
 intros H; [ apply RND_Max_canonic | apply RND_Min_canonic ].
Qed.

Theorem RND_ClosestUp_correct :
 forall r : R, Closest b radix r (RND_ClosestUp r).
intros r.
cut (RND_Min r <= r)%R; [ intros V1 | idtac ].
2: generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
    intros T3 T4; auto with real.
cut (r <= RND_Max r)%R; [ intros V2 | idtac ].
2: generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
    intros T3 T4; auto with real.
cut (forall v w : R, (v <= w)%R -> (0 <= w - v)%R); [ intros V3 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with v; ring_simplify (v + (w - v))%R;
    ring_simplify (v + 0)%R; auto with real.
cut (forall v w : R, (v <= w)%R -> (v - w <= 0)%R); [ intros V4 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with w; ring_simplify; auto with real.
unfold RND_ClosestUp in |- *;
 case (Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r))); 
 intros H; split;
 [ apply FcanonicBound with radix; apply RND_Max_canonic
 | intros f H1; fold FtoRradix in |- *
 | apply FcanonicBound with radix; apply RND_Min_canonic
 | intros f H1; fold FtoRradix in |- * ].
rewrite Rabs_right in H; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Faux.Rabsolu_left1 in H; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H2.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H); apply Ropp_le_contravar; unfold Rminus in |- *;
 apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
cut (Rabs (RND_Min r - r) < Rabs (RND_Max r - r))%R; auto with real;
 intros H'.
rewrite Faux.Rabsolu_left1 in H'; [ idtac | apply V4; auto with real ].
rewrite Rabs_right in H'; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
case (Rle_or_lt f r); intros H2.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Ropp_le_contravar; unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
apply Rle_trans with (RND_Max r - r)%R; auto with real; unfold Rminus in |- *;
 apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
Qed.



Definition RND_EvenClosest (r : R) :=
  match Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) with
  | left H =>
      match
        Rle_lt_or_eq_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) H
      with
      | left _ => RND_Max r
      | right _ =>
          match OddEvenDec (Fnum (RND_Min r)) with
          | left _ => RND_Max r
          | right _ => RND_Min r
          end
      end
  | right _ => RND_Min r
  end.


Theorem RND_EvenClosest_canonic :
 forall r : R, Fcanonic radix b (RND_EvenClosest r).
intros r; unfold RND_EvenClosest in |- *.
case (Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r))); intros H1.
case (Rle_lt_or_eq_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) H1);
 intros H2.
apply RND_Max_canonic.
case (OddEvenDec (Fnum (RND_Min r))); intros H3.
apply RND_Max_canonic.
apply RND_Min_canonic.
apply RND_Min_canonic.
Qed.

Theorem RND_EvenClosest_correct :
 forall r : R, EvenClosest b radix p r (RND_EvenClosest r).
intros r.
cut (RND_Min r <= r)%R; [ intros V1 | idtac ].
2: generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
    intros T3 T4; auto with real.
cut (r <= RND_Max r)%R; [ intros V2 | idtac ].
2: generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
    intros T3 T4; auto with real.
cut (forall v w : R, (v <= w)%R -> (0 <= w - v)%R); [ intros V3 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with v; ring_simplify; auto with real.
cut (forall v w : R, (v <= w)%R -> (v - w <= 0)%R); [ intros V4 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with w; ring_simplify; auto with real.
unfold RND_EvenClosest in |- *;
 case (Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r))); 
 intros H1.
case (Rle_lt_or_eq_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) H1);
 intros H2.
split.
split.
apply FcanonicBound with radix; apply RND_Max_canonic.
intros f H3; fold FtoRradix in |- *.
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Faux.Rabsolu_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H4.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
right; intros q H3.
generalize (ClosestMinOrMax b radix); unfold MinOrMaxP in |- *; intros T.
case (T r q); auto; intros H4; clear T.
Contradict H2; apply Rle_not_lt.
replace (FtoRradix (RND_Min r)) with (FtoRradix q).
elim H3; intros T1 T2; unfold FtoRradix in |- *; apply T2.
apply FcanonicBound with radix; apply RND_Max_canonic.
generalize (MinUniqueP b radix); unfold UniqueP in |- *; intros T;
 apply T with r; auto.
apply RND_Min_correct.
generalize (MaxUniqueP b radix); unfold UniqueP in |- *; intros T;
 apply T with r; auto.
apply RND_Max_correct.
case (OddEvenDec (Fnum (RND_Min r))); intros H3.
split.
split.
apply FcanonicBound with radix; apply RND_Max_canonic.
intros f H4; fold FtoRradix in |- *.
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Faux.Rabsolu_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
case (Req_EM_T (RND_Max r) (RND_Min r)); intros W.
right; intros q H4.
generalize (ClosestMinOrMax b radix); unfold MinOrMaxP in |- *; intros T.
case (T r q); auto; intros H5; clear T.
fold FtoRradix in |- *; rewrite W; generalize (MinUniqueP b radix);
 unfold UniqueP in |- *; intros T; apply T with r; 
 auto.
apply RND_Min_correct.
generalize (MaxUniqueP b radix); unfold UniqueP in |- *; intros T;
 apply T with r; auto.
apply RND_Max_correct.
left; unfold FNeven in |- *.
rewrite FcanonicFnormalizeEq; auto with arith;
 [ idtac | apply RND_Max_canonic ].
replace (RND_Max r) with (FSucc b radix p (RND_Min r)).
apply FoddSuc; auto.
unfold RND_Max, RND_Min in |- *; case (Rle_dec 0 r); intros W1.
unfold RND_Max_Pos in |- *.
case (Req_EM_T r (RND_Min_Pos r)); intros W2; auto.
Contradict W.
pattern r at 1 in |- *; rewrite W2.
apply sym_eq; unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdemEq with b p (isMax b radix); 
 auto.
apply MaxRoundedModeP with p; auto.
apply FcanonicBound with radix; apply RND_Min_canonic.
replace (FtoR radix (RND_Min r)) with (FtoR radix (RND_Min_Pos r));
 [ fold FtoRradix in |- *; rewrite <- W2; apply RND_Max_correct | idtac ].
fold FtoRradix in |- *; unfold RND_Min in |- *; auto with real.
case (Rle_dec 0 r); auto with real; intros W3; Contradict W1; auto with real.
unfold RND_Max_Pos in |- *.
case (Req_EM_T (- r) (RND_Min_Pos (- r))); intros W2; auto.
Contradict W.
cut (r = FtoRradix (Fopp (RND_Min_Pos (- r)))); [ intros W3 | idtac ].
pattern r at 1 in |- *; rewrite W3.
apply sym_eq; unfold FtoRradix in |- *;
 apply RoundedModeProjectorIdemEq with b p (isMax b radix); 
 auto.
apply MaxRoundedModeP with p; auto.
apply FcanonicBound with radix; apply RND_Min_canonic.
replace (FtoR radix (RND_Min r)) with (- FtoR radix (RND_Min_Pos (- r)))%R;
 [ fold FtoRradix in |- *; rewrite <- W3 | idtac ].
rewrite <- W2; rewrite Ropp_involutive; apply RND_Max_correct.
fold FtoRradix in |- *; unfold RND_Min in |- *; auto with real.
case (Rle_dec 0 r).
intros W4; Contradict W1; auto with real.
intros W4; unfold RND_Max_Pos in |- *;
 case (Req_EM_T (- r) (RND_Min_Pos (- r))); intros W5.
unfold FtoRradix in |- *; rewrite Fopp_correct; ring.
Contradict W2; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct; fold FtoRradix in |- *;
 rewrite <- W2; ring.
pattern (RND_Min_Pos (- r)) at 1 in |- *;
 rewrite <- (Fopp_Fopp (RND_Min_Pos (- r))).
rewrite <- FPredFopFSucc; auto with arith.
apply FSucPred; auto with arith.
apply FcanonicFopp; apply RND_Min_Pos_canonic; auto with real.
split.
split.
apply FcanonicBound with radix; apply RND_Min_canonic.
intros f H4; fold FtoRradix in |- *.
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Faux.Rabsolu_left1 in H1; [ idtac | apply V4; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Ropp_le_contravar; unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite <- H2.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
left; unfold FNeven in |- *.
rewrite FcanonicFnormalizeEq; auto with arith; apply RND_Min_canonic.
cut (Rabs (RND_Min r - r) < Rabs (RND_Max r - r))%R; auto with real;
 intros H'.
cut (Rabs (RND_Min r - r) < Rabs (RND_Max r - r))%R; auto with real;
 intros H''.
rewrite Faux.Rabsolu_left1 in H'; [ idtac | apply V4; auto with real ].
rewrite Rabs_right in H'; [ idtac | apply Rle_ge; apply V3; auto with real ].
split.
split.
apply FcanonicBound with radix; apply RND_Min_canonic.
intros f W1.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
case (Rle_or_lt f r); intros H2.
rewrite Faux.Rabsolu_left1; [ idtac | apply V4; auto with real ].
apply Ropp_le_contravar; unfold Rminus in |- *; apply Rplus_le_compat_r.
generalize (RND_Min_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
apply Rle_trans with (RND_Max r - r)%R; auto with real; unfold Rminus in |- *;
 apply Rplus_le_compat_r.
generalize (RND_Max_correct r); intros T; elim T; intros T1 T2; elim T2;
 intros T3 T4; auto with real.
right; intros q H3.
generalize (ClosestMinOrMax b radix); unfold MinOrMaxP in |- *; intros T.
case (T r q); auto; intros H4; clear T.
generalize (MinUniqueP b radix); unfold UniqueP in |- *; intros T;
 apply T with r; auto.
apply RND_Min_correct.
Contradict H''; apply Rle_not_lt.
replace (FtoRradix (RND_Max r)) with (FtoRradix q).
elim H3; intros T1 T2; unfold FtoRradix in |- *; apply T2.
apply FcanonicBound with radix; apply RND_Min_canonic.
generalize (MaxUniqueP b radix); unfold UniqueP in |- *; intros T;
 apply T with r; auto.
apply RND_Max_correct.
Qed.






End Round.
