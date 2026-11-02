import Lean
import Spec4Pbt.CorrectGen
import properties.wasm_module_ok.PlanReference.Transport

set_option autoImplicit false
set_option linter.unusedVariables false
namespace properties.wasm_module_ok.PlanReference.Contract

structure Input where
  «m» : properties.wasm_module_ok.PlanReference.ContractTransport.Type0
  deriving Lean.FromJson, Lean.ToJson
def encodeInput (input : Input) : Lean.Json := Lean.toJson input

def Goal
    (input : Input) : Prop :=
  true = true

def Premise
    (input : Input) : Prop :=
  (SpecTec.«Module_ok» input.«m»)

abbrev generator := CorrectGen Premise
abbrev generatorValue := Gen Input
def generatorSound (g : generatorValue) : Prop :=
  ∀ input, Gen.support g input → Premise input
def generatorComplete (g : generatorValue) : Prop :=
  ∀ input, Premise input → Gen.support g input

def property : Prop :=
  ∀ (input : Input),
    Premise input →
      Goal input

end properties.wasm_module_ok.PlanReference.Contract
