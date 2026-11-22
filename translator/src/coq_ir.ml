(** Typed target representation shared by the subsequent lowering stages.
    Source AL types remain attached to signatures until Data.lower resolves them. *)
type profile = { name : string }
type diagnostic = {
  stage : string;
  location : Util.Source.region;
  construct : string;
  reason : string;
}

type typ =
  | Unit | Bool | Nat | Int | Text
  | Type_parameter of string
  | Named of string * typ list
  | Product of typ list
  | List of typ | Option of typ
  | Function_ref of { parameters : string list; inputs : typ list; output : typ }

type binding = { name : string; typ : typ }
type scope = binding list

type expression = { typ : typ; term : term }
and term =
  | Variable of string
  | Literal of string
  | Constructor of string * expression list
  | Tuple of expression list
  | Projection of expression * string
  | Primitive of string * expression list
  | Lambda of binding list * expression
  | Apply of expression * expression list
  | Match_term of expression * (string * expression) list
  | Function of string

type call = { target : string; type_arguments : typ list; arguments : expression list; result : typ }
type action = { result : typ; node : action_node }
and action_node =
  | Return of expression
  | Invoke of call
  | Bind of binding * action * action
  | Guard of expression
  | Alternatives of action list
  | Unmatch
  | Error of string
  | Fresh
  | Choose of typ
  | Negate of action
  | Match of expression * (string * action) list
  | Local of binding * expression * action
  | Traverse of binding * expression * action
  | Primitive_action of string * expression list

type body = { call_name : string; parameters : binding list; result : typ; action : action }
type constructor = { constructor_name : string; fields : typ list }
type data_declaration =
  | Alias of string * string list * typ
  | Inductive of string * string list * constructor list
  | Record of string * string list * binding list

type data_module = { module_name : string; declarations : data_declaration list }

let diagnostic_to_json d =
  `Assoc ["stage", `String d.stage; "location", Util.Source.region_to_yojson d.location;
          "construct", `String d.construct; "reason", `String d.reason]
