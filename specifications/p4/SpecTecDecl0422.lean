import SpecTecDecl0421

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$resolve_inference'» (arg0 : typeIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$resolve_inference'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$resolve_inference:case_1:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$resolve_inference:case_1:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$resolve_inference» (arg0 : inference) (arg1 : inference) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨inference, SpecTecCall.«$resolve_inference» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$merge_constraint'» (arg0 : constraint) (arg1 : constraint) (arg2 : (_root_.List typeId)) (arg3 : constraint) (arg4 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$merge_constraint'» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$merge_constraint» (arg0 : constraint) (arg1 : constraint) (arg2 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$merge_constraint» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$merge_constraints» (arg0 : constraint) (arg1 : (_root_.List constraint)) (arg2 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$merge_constraints» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$gen_constraint» (arg0 : constraint) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeIR)) (arg3 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$gen_constraint» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$gen_constraint:case_1:iter:0» (arg0 : constraint) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List constraint)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constraint), SpecTecCall.«$gen_constraint:case_1:iter:0» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$gen_constraint_pair» (arg0 : constraint) (arg1 : typeIR) (arg2 : typeIR) (arg3 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$gen_constraint_pair» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$infer_pair» (arg0 : constraint) (arg1 : parameterIR) (arg2 : argumentIR) (arg3 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$infer_pair» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$infer:case_2:iter:6» (arg0 : constraint) (arg1 : (_root_.List argumentIR)) (arg2 : (_root_.List parameterIR)) (arg3 : (_root_.List constraint)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constraint), SpecTecCall.«$infer:case_2:iter:6» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$infer» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) (arg3 : (_root_.List argumentIR)) (arg4 : inference) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨inference, SpecTecCall.«$infer» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$resolve_type_alias» (arg0 : typeIR) (arg1 : (nameIR × (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(nameIR × (_root_.List typeIR)), SpecTecCall.«$resolve_type_alias» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def ConstructorType_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : constructorTargetIR) (arg3 : (_root_.List argumentIR)) (arg4 : constructorTypeIR) (arg5 : (_root_.List typeId)) (arg6 : (_root_.List id)) (arg7 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(constructorTypeIR × ((_root_.List typeId) × ((_root_.List id) × (_root_.List id)))), SpecTecCall.ConstructorType_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, (arg6, arg7)))))) finalSupply

namespace Notation.ConstructorType_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[15]⟩, ⟨stx[17]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ConstructorType_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.ConstructorType_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "(", x3, Lean.mkAtom ")", Lean.mkAtom ":", x4, Lean.mkAtom "<", Lean.mkAtom "#", x5, Lean.mkAtom ">", Lean.mkAtom "(", Lean.mkAtom "#", x6, Lean.mkAtom "#", x7, Lean.mkAtom ")"])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg " ( " term:51 " ) " " : " term:51 " < " " # " term:51 " > " " ( " " # " term:51 " # " term:51 " ) " : term
attribute [scoped macro SpecTec.Notation.ConstructorType_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ConstructorType_ok] unexpandRelationNotation
end Notation.ConstructorType_ok


noncomputable def «$instantiable» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : typeIR) (arg4 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$subst_type_i» (arg0 : cursor) (arg1 : instContext) (arg2 : typeIR) (arg3 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$subst_type_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def Constructor_inst (arg0 : cursor) (arg1 : instContext) (arg2 : prefixedNameIR) (arg3 : typeArgumentListIR) (arg4 : argumentListIR) (arg5 : constructorDef) (arg6 : typeArgumentListIR) (arg7 : (_root_.List id)) (arg8 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(constructorDef × (typeArgumentListIR × ((_root_.List id) × (_root_.List id)))), SpecTecCall.Constructor_inst arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, (arg7, arg8)))))) finalSupply

namespace Notation.Constructor_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[13]⟩, ⟨stx[17]⟩, ⟨stx[19]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Constructor_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.Constructor_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "<", x3, Lean.mkAtom ">", Lean.mkAtom "(", x4, Lean.mkAtom ")", Lean.mkAtom ":", x5, Lean.mkAtom "<", x6, Lean.mkAtom ">", Lean.mkAtom "(", Lean.mkAtom "#", x7, Lean.mkAtom "#", x8, Lean.mkAtom ")"])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " < " term:51 " > " " ( " term:51 " ) " " : " term:51 " < " term:51 " > " " ( " " # " term:51 " # " term:51 " ) " : term
attribute [scoped macro SpecTec.Notation.Constructor_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Constructor_inst] unexpandRelationNotation
end Notation.Constructor_inst


noncomputable def «$subst_type_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : typeIR) (arg3 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$subst_type_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_packet_in_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$V1Model_setup_packet_in_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$V1Model_setup_packet_out_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$V1Model_setup_packet_out_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$V1Model_setup_standard_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$V1Model_setup_standard_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$V1Model_setup_main_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_main_callee» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$V1Model_setup_parser_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_parser_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_verify_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_verify_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_ingress_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_ingress_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_egress_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_egress_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_check_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_check_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_deparse_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$V1Model_setup_deparse_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$eBPF_setup_packet_in_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$eBPF_setup_packet_in_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$eBPF_setup_main_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$eBPF_setup_main_callee» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$eBPF_setup_parse_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$eBPF_setup_parse_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$eBPF_setup_filter_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$eBPF_setup_filter_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

end SpecTec
