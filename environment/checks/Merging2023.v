From QuickChick Require Import QuickChick.
From Coq Require Import List Arith.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.
Inductive Even : nat -> Prop := E0 : Even 0 | ES : forall n, Even n -> Even (S (S n)).

Inductive Three : nat -> Prop := T0 : Three 0 | TS : forall n, Three n -> Three (S (S (S n))).
Derive DecOpt for (Even n).
Derive DecOpt for (Three n).
Derive ArbitrarySizedSuchThat for (fun n => Even n).
Derive ArbitrarySizedSuchThat for (fun n => Three n).
Merge (fun n => Even n) With (fun n => Three n) As Six.
Derive ArbitrarySizedSuchThat for (fun n => Six n).
QuickChick (forAll (genSizedST (fun n => Six n) 10) (fun x => match x with Some n => Nat.eqb (Nat.modulo n 6) 0 | None => false end)).
