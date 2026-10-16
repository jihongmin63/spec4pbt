import Lean
import pbt.SpectecRuntime.RunEval
set_option autoImplicit false
set_option linter.unusedVariables false
namespace AeSpec
open SpecTecExecution
inductive «expr» where
  | c0 : _root_.Int → «expr»
  | c1 : «expr» → «expr» → «expr»
  | c2 : «expr» → «expr» → «expr»
  deriving _root_.DecidableEq, _root_.Repr, _root_.Lean.ToJson, _root_.Lean.FromJson
inductive Call : Type → Type where
  | «Eval_expr» : «expr» → Call (_root_.Int)
def program : _root_.SpecTecExecution.ExecutableProgram Call where
  primitive := fun _ _ => _root_.False
  body := fun request => match request with
    | (Call.«Eval_expr» input0) =>
      .orElse ((let v_65787072 := input0; .bind (.guard ((match v_65787072 with | .c0 _ => true | _ => false) = true)) (fun _ => (match v_65787072 with | («expr».c0 v_6e) => .pure v_6e | _ => .abort "IL assignment mismatch")))) (fun _ => .orElse ((let v_65787072 := input0; .bind (.guard ((match v_65787072 with | .c1 _ _ => true | _ => false) = true)) (fun _ => (match v_65787072 with | («expr».c1 v_655f31 v_655f32) => .bind (.call (Call.«Eval_expr» v_655f31)) (fun callResult => (let v_6e5f31 := callResult; .bind (.call (Call.«Eval_expr» v_655f32)) (fun callResult => (let v_6e5f32 := callResult; .pure (v_6e5f31 + v_6e5f32))))) | _ => .abort "IL assignment mismatch")))) (fun _ => .orElse ((let v_65787072 := input0; .bind (.guard ((match v_65787072 with | .c2 _ _ => true | _ => false) = true)) (fun _ => (match v_65787072 with | («expr».c2 v_655f31 v_655f32) => .bind (.call (Call.«Eval_expr» v_655f31)) (fun callResult => (let v_6e5f31 := callResult; .bind (.call (Call.«Eval_expr» v_655f32)) (fun callResult => (let v_6e5f32 := callResult; .pure (v_6e5f31 - v_6e5f32))))) | _ => .abort "IL assignment mismatch")))) (fun _ => .unmatch)))
def «runEval_expr» (fuel : _root_.Nat) (input0 : «expr») : _root_.SpecTecExecution.RunResult (_root_.Int) :=
  _root_.SpecTecExecution.runEval program (_root_.SpecTecExecution.PrimitiveRunner.unavailable program) fuel (.call (Call.«Eval_expr» input0)) 0
def «Eval_expr» (arg0 : «expr») (arg1 : _root_.Int) : Prop :=
  ∃ final, _root_.SpecTecExecution.Eval program.erase (.call ⟨_, (Call.«Eval_expr» arg0)⟩) 0 (.success (.of arg1)) final
end AeSpec
