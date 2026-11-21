From QuickChick Require Import QuickChick Tactics Instances Classes DependentClasses.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import GenLow GenHigh.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.

Inductive Even : nat -> Prop :=
| even_zero : Even O
| even_step : forall n, Even n -> Even (S (S n)).

Derive ArbitrarySizedSuchThat for (fun n => Even n).
Derive SizedProofEqs for (fun n => Even n).
Derive SizeMonotonicSuchThatOpt for (fun n => Even n).
Derive GenSizedSuchThatCorrect for (fun n => Even n).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun n => Even n).

(* The proof term below is supplied by QuickChick's derived instances. *)
Definition even_generator : G (option nat) :=
  @arbitraryST _ (fun n => Even n) _.
Definition even_correct :=
  @STCorrect _ (fun n => Even n) even_generator _.

Check even_correct.
Print Assumptions even_correct.

Sample even_generator.
QuickChick (forAll even_generator (fun result =>
  match result with
  | Some n => Nat.even n
  | None => false
  end)).
