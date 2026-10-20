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

def profileId : String := "911ff0e366035279d1f488f20f5b2f16726d1e8223a11f1babac5e1d3a203818"

end «AeView»
