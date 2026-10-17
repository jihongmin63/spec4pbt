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

def profileId : String := "9a74738515874438a564f62d14b969bb668c13cdfaa2262486c45608d2408af0"

end «P4View»
