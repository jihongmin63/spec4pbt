Require Import Property.Original.
From Coq Require Import String Ascii ZArith.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import Types_0000 InductiveRelations.
Inductive predicate : Input -> Prop :=
| precondition : forall (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b646576616161 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b6465766161 : nat) (property_state_0 : State) (property_state_1 : State) (property_state_2 : State),
    g_fixture_rel_PropertyPremisePropertyPreced90171ae040_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 {| next_fresh := 0 |} (Success tt) property_state_0 ->
    g_fixture_rel_External_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 property_state_0 (Success (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661, w_70726f70657274796d6f6e6a616268626b6f6165616b646576616161)) property_state_1 ->
    g_fixture_rel_B_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661 property_state_1 (Success w_70726f70657274796d6f6e6a616268626b6f6165616b6465766161) property_state_2 ->
    predicate (mkInput w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161).
