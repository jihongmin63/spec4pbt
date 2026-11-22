From QuickChick Require Import QuickChick.
From Coq Require Import Arith.
Definition even_check := Nat.even.
Inductive Even : nat -> Prop :=
| E0 : Even 0
| ES : forall n, Even n -> Even (S (S n)).
Theorem test_even : forall n, Even n -> even_check n = true.
  quickchick 10.
Abort.
