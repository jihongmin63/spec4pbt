Require Import Property.Original.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
From CandidateSpec.Generated Require Import InductiveRelations_0000.

Inductive predicate : Original.Input -> Prop :=
| precondition : forall (x helper_value b c : nat)
    (middle final helper_final : State),
    g_fixture_rel_External_execute x {| next_fresh := 0 |}
      (Success b) middle ->
    g_fixture_rel_B_execute b middle (Success c) final ->
    g_candidate_rel_Helper_execute x final
      (Success helper_value) helper_final ->
    predicate (mkInput x).
