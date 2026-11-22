From QuickChick Require Import QuickChick.
From Coq Require Import Arith.
Import QcDefaultNotation.
Open Scope qc_scope.
Inductive Even : nat -> Prop :=
| E0 : Even 0
| ES : forall n, Even n -> Even (S (S n)).
Derive ArbitrarySizedSuchThat for (fun n => Even n).
QuickChick (forAll (genSizedST (fun n => Even n) 10)
  (fun x => match x with Some n => Nat.even n | None => false end)).
