From QuickChick Require Import QuickChick.
From Coq Require Import String Ascii.
From ALCoq Require Import Execution.
From P4Spec.Generated Require Import InductiveRelations.
Import QcDefaultNotation.
Require Extraction.
Derive Arbitrary for ascii.
Derive Arbitrary for string.

Record Input := mkInput { input_n : nat }.
#[global] Instance showInput : Show Input :=
  {| show := fun i => show (input_n i) |}.

Inductive predicate : Input -> Prop :=
| two_fresh : forall (n : nat) (first second : string) (middle final : State),
    g_p4_dec_fresh_x5f_typeId_execute {| next_fresh := 0 |}
      (Success first) middle ->
    g_p4_dec_fresh_x5f_typeId_execute middle (Success second) final ->
    predicate (mkInput n).

Definition encode_input (i : Input) : nat := input_n i.
Theorem generator_factory : forall x : Input, predicate x -> true = true.
Proof.
  quickchick 2.
  Extraction "fresh_generator.ml" GenSizedSuchThat_predicate_O encode_input.
  intros; reflexivity.
Qed.
Print Assumptions generator_factory.
