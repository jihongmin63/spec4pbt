Require Import Property.Original.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.

Inductive predicate : Original.Input -> Prop :=
| precondition : forall (x b c : nat) (middle final : State),
    g_fixture_rel_External_execute x {| next_fresh := 0 |}
      (Success b) middle ->
    g_fixture_rel_B_execute b middle (Success c) final ->
    predicate (mkInput x).
