import SpecTecDecl0429

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$bin_bxor» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_bxor» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_bor» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_bor» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$tableEntry_lpm_prefix'» (arg0 : value) (arg1 : _root_.Nat) (arg2 : _root_.Nat) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Nat, SpecTecCall.«$tableEntry_lpm_prefix'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$tableEntry_lpm_prefix» (arg0 : value) (arg1 : _root_.Nat) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Nat, SpecTecCall.«$tableEntry_lpm_prefix» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$bitacc_range_op» (arg0 : value) (arg1 : value) (arg2 : value) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bitacc_range_op» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$bitacc_offset_op» (arg0 : value) (arg1 : value) (arg2 : value) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bitacc_offset_op» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$bitacc_range_replace_op» (arg0 : value) (arg1 : value) (arg2 : value) (arg3 : value) (arg4 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bitacc_range_replace_op» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$bitacc_offset_replace_op» (arg0 : value) (arg1 : value) (arg2 : value) (arg3 : value) (arg4 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bitacc_offset_replace_op» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$bin_concat» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_concat» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$write_value_from_bits'» (arg0 : value) (arg1 : _root_.Nat) (arg2 : (_root_.List _root_.Bool)) (arg3 : (value × (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(value × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_from_bits'» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$write_values_from_bits'» (arg0 : (_root_.List value)) (arg1 : _root_.Nat) (arg2 : (_root_.List _root_.Bool)) (arg3 : ((_root_.List value) × (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List value) × (_root_.List _root_.Bool)), SpecTecCall.«$write_values_from_bits'» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$write_value_fields_from_bits'» (arg0 : (_root_.List fieldValue)) (arg1 : _root_.Nat) (arg2 : (_root_.List _root_.Bool)) (arg3 : ((_root_.List fieldValue) × (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List fieldValue) × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_fields_from_bits'» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$write_value_field_from_bits'» (arg0 : fieldValue) (arg1 : _root_.Nat) (arg2 : (_root_.List _root_.Bool)) (arg3 : (fieldValue × (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(fieldValue × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_field_from_bits'» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$write_value_from_bits» (arg0 : value) (arg1 : _root_.Nat) (arg2 : (_root_.List _root_.Bool)) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$write_value_from_bits» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$write_bits_from_value» (arg0 : value) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$write_bits_from_value:case_5:iter:1» (arg0 : (_root_.List value)) (arg1 : (_root_.List (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_5:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$write_bits_from_value:case_6:iter:1» (arg0 : (_root_.List value)) (arg1 : (_root_.List (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_6:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$write_bits_from_value:case_7:iter:3» (arg0 : (_root_.List value)) (arg1 : (_root_.List (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_7:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$write_bits_from_value:case_8:iter:3» (arg0 : (_root_.List value)) (arg1 : (_root_.List (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_8:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$write_bits_from_value:case_10:iter:3» (arg0 : (_root_.List value)) (arg1 : (_root_.List (_root_.List _root_.Bool))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_10:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def Lvalue_read (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : storageReference) (arg4 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.Lvalue_read arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.Lvalue_read
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Lvalue_read arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Lvalue_read.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Lvalue_read.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Lvalue_read] unexpandRelationNotation
end Notation.Lvalue_read


noncomputable def Lvalue_write (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : storageReference) (arg4 : value) (arg5 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Lvalue_write arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of (arg5))) finalSupply

namespace Notation.Lvalue_write
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Lvalue_write arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Lvalue_write.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":=", x4, Lean.mkAtom ":", x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " := " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Lvalue_write.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Lvalue_write] unexpandRelationNotation
end Notation.Lvalue_write


noncomputable def Copy_out_argument (arg0 : arch) (arg1 : cursor) (arg2 : evalContext) (arg3 : parameterIR) (arg4 : cursor) (arg5 : evalContext) (arg6 : (_root_.Option storageReference)) (arg7 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Copy_out_argument arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of (arg7))) finalSupply

namespace Notation.Copy_out_argument
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[10]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_out_argument arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.Copy_out_argument.relationNotation
        #[x0, Lean.mkAtom "|-", x1, x2, x3, Lean.mkAtom "@", x4, x5, x6, Lean.mkAtom "~>", x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_out_argument.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_out_argument] unexpandRelationNotation
end Notation.Copy_out_argument


noncomputable def Copy_out_inner (arg0 : arch) (arg1 : cursor) (arg2 : evalContext) (arg3 : parameterListIR) (arg4 : cursor) (arg5 : evalContext) (arg6 : (_root_.List (_root_.Option storageReference))) (arg7 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Copy_out_inner arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of (arg7))) finalSupply

namespace Notation.Copy_out_inner
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[10]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_out_inner arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.Copy_out_inner.relationNotation
        #[x0, Lean.mkAtom "|-", x1, x2, x3, Lean.mkAtom "@", x4, x5, x6, Lean.mkAtom "~>", x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_out_inner.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_out_inner] unexpandRelationNotation
end Notation.Copy_out_inner


noncomputable def Copy_out (arg0 : cursor) (arg1 : arch) (arg2 : cursor) (arg3 : evalContext) (arg4 : parameterListIR) (arg5 : cursor) (arg6 : evalContext) (arg7 : (_root_.List (_root_.Option storageReference))) (arg8 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Copy_out arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7⟩) 0 (.success (.of (arg8))) finalSupply

namespace Notation.Copy_out
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_out arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.Copy_out.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, Lean.mkAtom "@", x5, x6, x7, Lean.mkAtom "~>", x8])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_out.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_out] unexpandRelationNotation
end Notation.Copy_out


noncomputable def V1Model_copy_meta_fields (arg0 : evalContext) (arg1 : evalContext) (arg2 : arch) (arg3 : (_root_.List nameIR)) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.V1Model_copy_meta_fields arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.V1Model_copy_meta_fields
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_copy_meta_fields arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_copy_meta_fields.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_copy_meta_fields.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_copy_meta_fields] unexpandRelationNotation
end Notation.V1Model_copy_meta_fields


noncomputable def PSA_ingress_init_parser_input_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_ingress_init_parser_input_metadata arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.PSA_ingress_init_parser_input_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_parser_input_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_parser_input_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_parser_input_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_parser_input_metadata] unexpandRelationNotation
end Notation.PSA_ingress_init_parser_input_metadata


noncomputable def PSA_ingress_init_input_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_ingress_init_input_metadata arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.PSA_ingress_init_input_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_input_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_input_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_input_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_input_metadata] unexpandRelationNotation
end Notation.PSA_ingress_init_input_metadata


noncomputable def PSA_ingress_init_output_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_ingress_init_output_metadata arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.PSA_ingress_init_output_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_output_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_output_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_output_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_output_metadata] unexpandRelationNotation
end Notation.PSA_ingress_init_output_metadata


noncomputable def PSA_ingress_init_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_ingress_init_metadata arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.PSA_ingress_init_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_metadata] unexpandRelationNotation
end Notation.PSA_ingress_init_metadata


noncomputable def PSA_egress_init_parser_input_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_parser_input_metadata arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.PSA_egress_init_parser_input_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_parser_input_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_parser_input_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_parser_input_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_parser_input_metadata] unexpandRelationNotation
end Notation.PSA_egress_init_parser_input_metadata


noncomputable def PSA_egress_init_input_metadata (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : _root_.String) (arg4 : _root_.Int) (arg5 : _root_.Int) (arg6 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_input_metadata arg0 arg1 arg2 arg3 arg4 arg5⟩) 0 (.success (.of (arg6))) finalSupply

namespace Notation.PSA_egress_init_input_metadata
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_input_metadata arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_input_metadata.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, x5, Lean.mkAtom ":", x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_input_metadata.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_input_metadata] unexpandRelationNotation
end Notation.PSA_egress_init_input_metadata

end SpecTec
