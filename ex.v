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


Require Import AllFloat.
Require Import FminOp.

Definition radix := 2%Z.

Definition precision := 53.

Definition b := Bound (Z2pos (Zpower_nat radix precision)) 10.



Check rToZero.

Let rToZero := rToZero radix b precision.

Let rClosestEven := rClosestEven radix b precision.

Eval compute in (rToZero (Float 999999999999999 12)).

Eval compute in (rClosestEven (Float 1005 12)).

Eval compute in (rClosestEven (Float 1015 12)).
