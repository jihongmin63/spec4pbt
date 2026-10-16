import Lean
import pbt.SpectecRuntime.RunEval
set_option autoImplicit false
set_option linter.unusedVariables false
namespace PartialSpec
open SpecTecExecution
structure «result» where
  «VALUE» : _root_.Int
  «TRACE» : _root_.Int
  deriving _root_.DecidableEq, _root_.Repr, _root_.Lean.ToJson, _root_.Lean.FromJson
inductive Call : Type → Type where
  | «Eval» : _root_.Int → Call («result»)
def program : _root_.SpecTecExecution.ExecutableProgram Call where
  primitive := fun _ _ => _root_.False
  body := fun request => match request with
    | (Call.«Eval» input0) =>
      .orElse ((let v_6e := input0; .pure ({ «VALUE» := (v_6e + (_root_.Int.ofNat (1 : _root_.Nat))), «TRACE» := v_6e } : «result»))) (fun _ => .unmatch)
def «runEval» (fuel : _root_.Nat) (input0 : _root_.Int) : _root_.SpecTecExecution.RunResult («result») :=
  _root_.SpecTecExecution.runEval program (_root_.SpecTecExecution.PrimitiveRunner.unavailable program) fuel (.call (Call.«Eval» input0)) 0
def «Eval» (arg0 : _root_.Int) (arg1 : «result») : Prop :=
  ∃ final, _root_.SpecTecExecution.Eval program.erase (.call ⟨_, (Call.«Eval» arg0)⟩) 0 (.success (.of arg1)) final
end PartialSpec
