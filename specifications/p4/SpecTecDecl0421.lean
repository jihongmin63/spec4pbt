import SpecTecDecl0420

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:structTypeIR_3:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «ParserSelect_ok:rule:iter:6» (arg0 : typingContext) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ParserSelect_ok:rule:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def TableType_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : name) (arg3 : typingContext) (arg4 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × typeIR), SpecTecCall.TableType_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableType_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableType_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableType_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableType_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableType_ok] unexpandRelationNotation
end Notation.TableType_ok


noncomputable def CallableType_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : callableTargetIR) (arg3 : typeArgumentListIR) (arg4 : (_root_.List argumentIR)) (arg5 : callableTypeIR) (arg6 : (_root_.List typeId)) (arg7 : (_root_.List id)) (arg8 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(callableTypeIR × ((_root_.List typeId) × ((_root_.List id) × (_root_.List id)))), SpecTecCall.CallableType_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, (arg7, arg8)))))) finalSupply

namespace Notation.CallableType_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[14]⟩, ⟨stx[18]⟩, ⟨stx[20]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.CallableType_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.CallableType_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "<", x3, Lean.mkAtom ">", Lean.mkAtom "(", x4, Lean.mkAtom ")", Lean.mkAtom ":", x5, Lean.mkAtom "<", Lean.mkAtom "#", x6, Lean.mkAtom ">", Lean.mkAtom "(", Lean.mkAtom "#", x7, Lean.mkAtom "#", x8, Lean.mkAtom ")"])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " < " term:51 " > " " ( " term:51 " ) " " : " term:51 " < " " # " term:51 " > " " ( " " # " term:51 " # " term:51 " ) " : term
attribute [scoped macro SpecTec.Notation.CallableType_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.CallableType_ok] unexpandRelationNotation
end Notation.CallableType_ok


noncomputable def «Call_ok:definedFunctionTypeIR:iter:3» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Call_ok:definedFunctionTypeIR:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:definedFunctionTypeIR:iter:5» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:definedFunctionTypeIR:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:externFunctionTypeIR:iter:3» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Call_ok:externFunctionTypeIR:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:externFunctionTypeIR:iter:5» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:externFunctionTypeIR:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:non-abstract:iter:3» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Call_ok:non-abstract:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:non-abstract:iter:5» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:non-abstract:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:abstract:iter:3» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Call_ok:abstract:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_ok:abstract:iter:5» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:abstract:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Inst_ok:package:iter:2» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Inst_ok:package:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Inst_ok:package:iter:4» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Inst_ok:package:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Inst_ok:non-package:iter:2» (arg0 : inference) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«Inst_ok:non-package:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Inst_ok:non-package:iter:4» (arg0 : inference) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«Inst_ok:non-package:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$reduce_serenum» (arg0 : typedExpressionIR) (arg1 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$reduce_serenum» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ParserSelect_ok:rule:iter:2» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«ParserSelect_ok:rule:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$reduce_serenum_unary» (arg0 : typedExpressionIR) (arg1 : (typeIR → (SpecTecCall _root_.Bool))) (arg2 : (_root_.Option typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typedExpressionIR), SpecTecCall.«$reduce_serenum_unary» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$reduce_serenum_binary» (arg0 : typedExpressionIR) (arg1 : typedExpressionIR) (arg2 : (typeIR → typeIR → (SpecTecCall _root_.Bool))) (arg3 : (_root_.Option (typedExpressionIR × typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (typedExpressionIR × typedExpressionIR)), SpecTecCall.«$reduce_serenum_binary» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_unary» (arg0 : typedExpressionIR) (arg1 : typeIR) (arg2 : (_root_.Option typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typedExpressionIR), SpecTecCall.«$cast_unary» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_binary» (arg0 : typedExpressionIR) (arg1 : typedExpressionIR) (arg2 : (_root_.Option (typedExpressionIR × typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (typedExpressionIR × typedExpressionIR)), SpecTecCall.«$cast_binary» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$result_concat» (arg0 : typeIR) (arg1 : typeIR) (arg2 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$result_concat» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$is_valid_bitslice» (arg0 : typeIR) (arg1 : _root_.Nat) (arg2 : _root_.Nat) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_valid_bitslice» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$is_concrete_extern_object» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_concrete_extern_object» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subst_externMethodTypeDefEnv» (arg0 : externMethodTypeDefEnv) (arg1 : externMethodTypeDefEnv) (arg2 : externMethodTypeDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externMethodTypeDefEnv, SpecTecCall.«$subst_externMethodTypeDefEnv» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$is_table_application» (arg0 : typedExpressionIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_table_application» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_action_partial_ok:rule:iter:2» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Call_action_partial_ok:rule:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_action_default_ok:rule:iter:2» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Call_action_default_ok:rule:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
