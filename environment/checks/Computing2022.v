From QuickChick Require Import QuickChick LazyList.
From Coq Require Import List Arith.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.
Inductive Even : nat -> Prop := E0 : Even 0 | ES : forall n, Even n -> Even (S (S n)).

Derive DecOpt for (Even n).
Derive ArbitrarySizedSuchThat for (fun n => Even n).
Derive EnumSizedSuchThat for (fun n => Even n).
Example accepts_even : @decOpt (Even 6) _ 20 = Some true. Proof. reflexivity. Qed.
Example rejects_odd : @decOpt (Even 5) _ 20 = Some false. Proof. reflexivity. Qed.
QuickChick (forAll (genSizedST (fun n => Even n) 10) (fun x => match x with Some n => Nat.even n | None => false end)).

Definition enumerated := LazyList_to_list
  (Enumerators.run (@enumSizeST nat Even _ 3) 3).
Example enumeration_includes_six : List.In (Some 6) enumerated.
Proof. simpl; auto. Qed.
Example enumeration_only_even : List.forallb
  (fun x => match x with Some n => Nat.even n | None => true end) enumerated = true.
Proof. reflexivity. Qed.
