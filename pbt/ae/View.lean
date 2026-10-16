import Lean
import «specifications».«ae».«Spec»

namespace «AeView»

abbrev Input := _root_.«AeSpec».«expr»
abbrev Observation := _root_.«Int»
abbrev FullOutput := _root_.«Int»

def encodeInput : Input → _root_.Lean.Json := _root_.Lean.ToJson.toJson
def decodeInput : _root_.Lean.Json → _root_.Except _root_.String Input := _root_.Lean.FromJson.fromJson?
def decodeObservation : _root_.Lean.Json → _root_.Except _root_.String Observation := _root_.Lean.FromJson.fromJson?

def project (full : FullOutput) : Observation :=
  full

def Specification (input : Input) (observation : Observation) : Prop :=
  ∃ full : FullOutput,
    (_root_.«AeSpec».«Eval_expr» (input) (full)) ∧
    project full = observation

def profileId : String := "b10c76ca96f2f711e2f47be96e49586bd95a04340f80a5cc43e21a2633fcaad0"

end «AeView»
