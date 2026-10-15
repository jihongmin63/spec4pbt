import SpecTecDecl0430

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def PSA_egress_init_output_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_output_metadata arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.PSA_egress_init_output_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_output_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_output_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_output_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_output_metadata] unexpandRelationNotation
end Notation.PSA_egress_init_output_metadata


noncomputable def PSA_egress_init_deparser_input_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_deparser_input_metadata arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.PSA_egress_init_deparser_input_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_deparser_input_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_deparser_input_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_deparser_input_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_deparser_input_metadata] unexpandRelationNotation
end Notation.PSA_egress_init_deparser_input_metadata


noncomputable def PSA_egress_init_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : _root_.Int) (arg5 : _root_.Int) (arg6 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_metadata arg0 arg1 arg2 arg3 arg4 arg5⟩) 0 (.success (.of (arg6))) finalSupply

namespace Notation.PSA_egress_init_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, x5, Lean.mkAtom ":", x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_metadata] unexpandRelationNotation
end Notation.PSA_egress_init_metadata


noncomputable def «$bin_eq» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_9:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_9:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_10:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_10:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_11:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_11:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_12:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_12:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_13:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_13:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_14:iter:4» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_14:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_15:iter:4» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_15:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_16:iter:4» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_16:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_ne» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_ne» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_op» (arg0 : binop) (arg1 : value) (arg2 : value) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_op» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_op» (arg0 : typeIR) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_op» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default» (arg0 : typeIR) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$default» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$default:case_10:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$default:case_10:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$default:case_13:iter:3» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_13:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default:case_14:iter:3» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_14:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default:case_15:iter:3» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_15:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_to_enum» (arg0 : enumTypeIR) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_to_enum» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_to_enum'» (arg0 : typeId) (arg1 : typeIR) (arg2 : (_root_.List valueFieldIR)) (arg3 : value) (arg4 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_to_enum'» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$cast_bool» (arg0 : typeIR) (arg1 : boolValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_bool» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_int» (arg0 : typeIR) (arg1 : integerValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_int» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_error» (arg0 : typeIR) (arg1 : errorValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_error» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_list» (arg0 : typeIR) (arg1 : listValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_list» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_list:case_1:iter:1» (arg0 : typeIR) (arg1 : (_root_.List value)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_list:case_1:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_tuple» (arg0 : typeIR) (arg1 : tupleValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_tuple» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_tuple:case_1:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_tuple:case_1:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_enum» (arg0 : typeIR) (arg1 : enumValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_enum» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence» (arg0 : typeIR) (arg1 : sequenceValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_sequence» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence:case_2:iter:1» (arg0 : typeIR) (arg1 : (_root_.List value)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_sequence:case_2:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
