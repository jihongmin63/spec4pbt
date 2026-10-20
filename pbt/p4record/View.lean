import Lean
import «specifications».«p4record».«Generated».«Transport»

namespace «P4View»

abbrev Input := _root_.«P4Observation».«Type0»
abbrev Observation := _root_.«P4Observation».«Type0»
abbrev FullOutput := _root_.«P4Observation».«Type1»

def encodeInput : Input → _root_.Lean.Json := _root_.Lean.ToJson.toJson
def decodeInput : _root_.Lean.Json → _root_.Except _root_.String Input := _root_.Lean.FromJson.fromJson?
def decodeObservation : _root_.Lean.Json → _root_.Except _root_.String Observation := _root_.Lean.FromJson.fromJson?

def project (full : FullOutput) : Observation :=
  (full).«VALUE»

def Specification (input : Input) (observation : Observation) : Prop :=
  ∃ full : FullOutput,
    (_root_.«P4Observation».«Relation0» (input) (full)) ∧
    project full = observation

def profileId : String := "8c6897c0bce877a6f970c424a294963470bc47535f97a62ae2dbbd6f3af77bba"

end «P4View»
