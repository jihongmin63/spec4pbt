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

def profileId : String := "a17714dbff9d470ef49bd5bf7ae56c88880cd791050b27c8bb9776ecb2257879"

end «PartialView»
