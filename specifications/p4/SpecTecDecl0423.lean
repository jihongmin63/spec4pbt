import SpecTecDecl0422

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$PSA_setup_main_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_main_callee» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$PSA_setup_ingress_packet_in_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_packet_in_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_packet_out_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_packet_out_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_parser_input_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_parser_input_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_input_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_input_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_output_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_output_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_pipeline_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_ingress_pipeline_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_ingress_parser_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_ingress_parser_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_ingress_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_ingress_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_ingress_deparser_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_ingress_deparser_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_egress_packet_in_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_packet_in_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_packet_out_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_packet_out_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_parser_input_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_parser_input_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_input_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_input_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_output_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_output_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_deparser_input_metadata_argument» (arg0 : evalContext) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_deparser_input_metadata_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_pipeline_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_egress_pipeline_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_egress_parser_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_egress_parser_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_egress_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_egress_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$PSA_setup_egress_deparser_callee» (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$PSA_setup_egress_deparser_callee» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$sizeof_minSizeInBits'» (arg0 : typeIR) (arg1 : _root_.Nat) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_minSizeInBits'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_8:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_minSizeInBits':case_8:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_11:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_minSizeInBits':case_11:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_12:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_minSizeInBits':case_12:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_13:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_minSizeInBits':case_13:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBits» (arg0 : typeIR) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$sizeof_minSizeInBits» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_minSizeInBytes» (arg0 : typeIR) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$sizeof_minSizeInBytes» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBits'» (arg0 : typeIR) (arg1 : _root_.Nat) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_8:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_8:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_11:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_11:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_12:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_12:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_13:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_13:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
