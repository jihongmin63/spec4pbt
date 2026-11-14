import WasmEmbedding

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std generator_rust

/-- Both the Aeneas computation and the Rust Result must return successfully. -/
def ReplayReturns (config : wasm.Config) (tape : wasm.choices.Tape)
    (output : wasm.ast.Module) : Prop :=
  ∃ finalState : wasm.choices.Choices,
    wasm.replay config tape = Result.ok (.Ok (output, finalState))

def SampleReturns (config : wasm.Config) (seed : U64)
    (output : wasm.ast.Module) : Prop :=
  ∃ finalState : wasm.choices.Choices,
    wasm.sample config seed = Result.ok (.Ok (output, finalState))

/-- Fixed-configuration support of the executable replay interface. -/
def ReplaySupport (config : wasm.Config) (module : SpecTec.module) : Prop :=
  ∃ tape output, ReplayReturns config tape output ∧ embed output = module

/-- Seed support is deliberately separate from arbitrary finite choice tapes. -/
def SampleSupport (config : wasm.Config) (module : SpecTec.module) : Prop :=
  ∃ seed output, SampleReturns config seed output ∧ embed output = module

def Soundness : Prop :=
  ∀ config module, ReplaySupport config module → SpecTec.Module_ok module

def SamplingSoundness : Prop :=
  ∀ config module, SampleSupport config module → SpecTec.Module_ok module

/-- The unrestricted original specification; no fragment or renaming quotient. -/
def Completeness : Prop :=
  ∀ module, SpecTec.Module_ok module → ∃ config, ReplaySupport config module

/-- A separate claim: a successful arbitrary tape need not be reachable from a seed. -/
def SamplingCompleteness : Prop :=
  ∀ module, SpecTec.Module_ok module → ∃ config, SampleSupport config module

/-- A bounded target must be supplied independently of generator support. -/
def CompleteFor (target : wasm.Config → SpecTec.module → Prop) : Prop :=
  ∀ config module, SpecTec.Module_ok module → target config module →
    ReplaySupport config module

end RustWasm
