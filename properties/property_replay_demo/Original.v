From QuickChick Require Import QuickChick.
From Coq Require Import String.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
Import QcDefaultNotation.
Open Scope string_scope.

Record Input := mkInput { input_x : nat }.
#[global] Instance showInput : Show Input :=
  {| show := fun i => show (input_x i) |}.

(* Each premise applies the already translated relation.  The intermediate
   state is a constructor witness and is passed to the next premise. *)
Inductive predicate : Input -> Prop :=
| precondition : forall (x b c : nat) (middle final : State),
    g_fixture_rel_External_execute x {| next_fresh := 0 |}
      (Success b) middle ->
    g_fixture_rel_B_execute b middle (Success c) final ->
    predicate (mkInput x).

Definition encode_input (i : Input) : string :=
  "{""x"":{""type"":""nat"",""value"":""" ++
  show (input_x i) ++ """}}".
