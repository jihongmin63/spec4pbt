From QuickChick Require Import QuickChick.
From Coq Require Import String Ascii ZArith.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import Types_0000 InductiveRelations.
Import QcDefaultNotation.
Open Scope string_scope.

Definition property_utf8_scalar (n : nat) : string :=
  let byte n := Ascii.ascii_of_nat n in
  if Nat.ltb n 128 then String (byte n) EmptyString else
  if Nat.ltb n 2048 then
    String (byte (192 + n / 64)) (String (byte (128 + n mod 64)) EmptyString)
  else if Nat.ltb n 65536 then
    String (byte (224 + n / 4096))
      (String (byte (128 + (n / 64) mod 64))
        (String (byte (128 + n mod 64)) EmptyString))
  else String (byte (240 + n / 262144))
    (String (byte (128 + (n / 4096) mod 64))
      (String (byte (128 + (n / 64) mod 64))
        (String (byte (128 + n mod 64)) EmptyString))).
Fixpoint property_gen_text (size : nat) : G string :=
  match size with
  | O => returnGen EmptyString
  | S rest => bindGen (choose (0, 1112063)%nat) (fun index =>
      let scalar := if Nat.ltb index 55296 then index else (index + 2048)%nat in
      bindGen (property_gen_text rest) (fun tail =>
        returnGen (String.append (property_utf8_scalar scalar) tail)))
  end.
#[global] Instance property_gen_sized_text : GenSized string :=
  {| arbitrarySized := fun size => bindGen (choose (0, size)%nat) property_gen_text |}.

Record Input := mkInput { input_w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 : nat }.
#[global] Instance showInput : Show Input :=
  {| show := fun _ => "Input" |}.

Inductive predicate : Input -> Prop :=
| precondition : forall (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b646576616161 : nat) (w_70726f70657274796d6f6e6a616268626b6f6165616b6465766161 : nat) (property_state_0 : State) (property_state_1 : State) (property_state_2 : State),
    g_fixture_rel_PropertyPremisePropertyPreced90171ae040_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 {| next_fresh := 0 |} (Success tt) property_state_0 ->
    g_fixture_rel_External_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 property_state_0 (Success (w_70726f70657274796d6f6e6a616268626b6f6165616b64657661, w_70726f70657274796d6f6e6a616268626b6f6165616b646576616161)) property_state_1 ->
    g_fixture_rel_B_execute w_70726f70657274796d6f6e6a616268626b6f6165616b64657661 property_state_1 (Success w_70726f70657274796d6f6e6a616268626b6f6165616b6465766161) property_state_2 ->
    predicate (mkInput w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161).

From Coq Require Import String Ascii Bool ZArith DecimalString.
Open Scope string_scope.

Definition property_json_hex (n : nat) : ascii :=
  Ascii.ascii_of_nat (if Nat.ltb n 10 then 48 + n else 87 + n).
Definition property_json_escape_char (c : ascii) : string :=
  let n := Ascii.nat_of_ascii c in
  if Nat.eqb n 34 then "\"""
  else if Nat.eqb n 92 then "\\"
  else if Nat.ltb n 32 then
    String.append "\u00"
      (String (property_json_hex (Nat.div n 16))
        (String (property_json_hex (Nat.modulo n 16)) EmptyString))
  else String c EmptyString.
Fixpoint property_json_escape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String.append (property_json_escape_char c)
                                 (property_json_escape rest)
  end.
Definition property_json_quote (s : string) : string :=
  String.append """" (String.append (property_json_escape s) """").
Definition property_json_nat (n : nat) : string :=
  String.append "{""type"":""nat"",""value"":"""
    (String.append (NilZero.string_of_uint (Nat.to_uint n)) """}").
Definition property_json_int (n : Z) : string :=
  String.append "{""type"":""int"",""value"":"""
    (String.append (NilZero.string_of_int (Z.to_int n)) """}").
Definition property_json_text (s : string) : string :=
  String.append "{""type"":""text"",""value"":"
    (String.append (property_json_quote s) "}").
Definition property_json_bool (b : bool) : string :=
  if b then "{""type"":""bool"",""value"":true}" else "{""type"":""bool"",""value"":false}".


Definition encode_input (i : Input) : string :=
  (String.append "{" (String.append """x"":" (String.append (property_json_nat (input_w_70726f70657274796d6f6e6a616268626b6f6165616b64657661616161 i)) "}"))).
