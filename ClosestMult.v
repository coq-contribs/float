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


(****************************************************************************
                                                                             
          IEEE754  :  FroundMult                                                 
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export FroundMult.
Require Export ClosestProp.
Section FRoundP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Coercion Local FtoRradix := FtoR radix.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem closestLessMultPos :
 forall (p : float) (r : R),
 Closest b radix r p -> (0 <= r)%R -> (p <= 2%nat * r)%R.
intros p r H' H'0.
case ClosestMinOrMax with (1 := H'); intros H'3.
apply Rle_trans with r; auto with real.
apply isMin_inv1 with (1 := H'3).
case (MinEx b radix precision) with (r := r); auto with arith.
intros min Hmin.
apply Rle_trans with (min + p)%R; auto with real.
apply Rplus_le_reg_l with (r := (- p)%R).
replace (- p + p)%R with 0%R; [ idtac | ring ].
replace (- p + (min + p))%R with (FtoRradix min);
 [ apply (RleMinR0 b radix precision) with (r := r); auto | ring ].
apply Rplus_le_reg_l with (r := (- r)%R).
apply Rplus_le_reg_l with (r := (- min)%R).
replace (- min + (- r + (min + p)))%R with (Rabs (p - r)).
replace (- min + (- r + 2%nat * r))%R with (Rabs (min - r)).
case H'.
intros H'1 H'2; apply H'2; auto.
case Hmin; auto.
rewrite Faux.Rabsolu_left1; simpl in |- *.
ring; auto.
apply Rle_minus; apply isMin_inv1 with (1 := Hmin).
rewrite Rabs_right; simpl in |- *.
ring; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
replace (r + 0)%R with r; [ idtac | ring ].
replace (r + (p - r))%R with (FtoRradix p);
 [ apply isMax_inv1 with (1 := H'3) | ring ].
Qed.
 
Theorem closestLessMultNeg :
 forall (p : float) (r : R),
 Closest b radix r p -> (r <= 0)%R -> (2%nat * r <= p)%R.
intros p r H' H'0.
replace (2%nat * r)%R with (- (2%nat * - r))%R; [ idtac | ring ].
replace (FtoRradix p) with (- - p)%R;
 [ unfold FtoRradix in |- *; rewrite <- Fopp_correct | ring ].
apply Ropp_le_contravar.
apply closestLessMultPos; auto.
apply ClosestOpp; auto.
replace 0%R with (-0)%R; [ auto with real | ring ].
Qed.
 
Theorem closestLessMultAbs :
 forall (p : float) (r : R),
 Closest b radix r p -> (Rabs p <= 2%nat * Rabs r)%R.
intros p r H'; case (Rle_or_lt 0 r); intros H'1.
repeat rewrite Rabs_right; auto with real.
apply closestLessMultPos; auto.
apply Rle_ge;
 apply (RleRoundedR0 b radix precision) with (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
repeat rewrite Faux.Rabsolu_left1; auto.
replace (2%nat * - r)%R with (- (2%nat * r))%R;
 [ apply Ropp_le_contravar | ring ].
apply closestLessMultNeg; auto.
apply Rlt_le; auto.
apply Rlt_le; auto.
apply
 (RleRoundedLessR0 b radix precision) with (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
apply Rlt_le; auto.
Qed.
End FRoundP.