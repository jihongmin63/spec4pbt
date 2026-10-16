import Lean
import «specifications».«record».«Spec»

namespace «PartialView»

abbrev Input := _root_.«Int»
abbrev Observation := _root_.«Int»
abbrev FullOutput := _root_.«PartialSpec».«result»

def encodeInput : Input → _root_.Lean.Json := _root_.Lean.ToJson.toJson
def decodeInput : _root_.Lean.Json → _root_.Except _root_.String Input := _root_.Lean.FromJson.fromJson?
def decodeObservation : _root_.Lean.Json → _root_.Except _root_.String Observation := _root_.Lean.FromJson.fromJson?

def project (full : FullOutput) : Observation :=
  (full).«VALUE»

def Specification (input : Input) (observation : Observation) : Prop :=
  ∃ full : FullOutput,
    (_root_.«PartialSpec».«Eval» (input) (full)) ∧
    project full = observation

def profileId : String := "36ac62eaa4a7dd91f239df0557a1bade878b677c80bac97dae8582e2899f87d5"

end «PartialView»
