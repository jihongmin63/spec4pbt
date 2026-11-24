Require Import Property.Original.
From Coq Require Import String Ascii ZArith.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import Types_0000 InductiveRelations.
Inductive predicate : Input -> Prop :=
| precondition : forall (w_70726f70657274796f6661616d65686e6f65646265616a6a7661616161 : nat) (w_70726f70657274796f6661616d65686e6f65646265616a6a7661 : nat) (w_70726f70657274796f6661616d65686e6f65646265616a6a76616161 : nat) (w_70726f70657274796f6661616d65686e6f65646265616a6a766161 : nat) (property_state_0 : State) (property_state_1 : State),
    g_fixture_rel_External_execute w_70726f70657274796f6661616d65686e6f65646265616a6a7661616161 {| next_fresh := 0 |} (Success (w_70726f70657274796f6661616d65686e6f65646265616a6a7661, w_70726f70657274796f6661616d65686e6f65646265616a6a76616161)) property_state_0 ->
    g_fixture_rel_B_execute w_70726f70657274796f6661616d65686e6f65646265616a6a7661 property_state_0 (Success w_70726f70657274796f6661616d65686e6f65646265616a6a766161) property_state_1 ->
    predicate (mkInput w_70726f70657274796f6661616d65686e6f65646265616a6a7661616161).
