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
