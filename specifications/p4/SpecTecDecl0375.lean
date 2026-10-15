import SpecTecDecl0374

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$extend_map:case_1:iter:9» (K : Type) (V : Type) (arg0 : (_root_.List K)) (arg1 : (_root_.List V)) (arg2 : (_root_.List (pair K V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:9» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$extend_map» (K : Type) (V : Type) (arg0 : (map K V)) (arg1 : (map K V)) (arg2 : (map K V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map K V), SpecTecCall.«$extend_map» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$print_» (X : Type) [_root_.SpecTecPrint X] (arg0 : X) (arg1 : _root_.String) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.String, SpecTecCall.«$print_» X arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$modulo» (arg0 : _root_.Nat) (arg1 : _root_.Nat) (arg2 : (_root_.Option _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$modulo» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$modulo_42» (arg0 : _root_.Nat) (arg1 : _root_.Nat) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Nat, SpecTecCall.«$modulo_42» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$name» (arg0 : name) (arg1 : nameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameIR, SpecTecCall.«$name» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableCustomName» (arg0 : tableCustomName) (arg1 : nameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameIR, SpecTecCall.«$tableCustomName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$fresh_typeId» (arg0 : typeId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeId, SpecTecCall.«$fresh_typeId» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$fresh_typeIds» (arg0 : _root_.Nat) (arg1 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeId), SpecTecCall.«$fresh_typeIds» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$objectId_ends_with» (arg0 : objectId) (arg1 : nameIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$objectId_ends_with» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bitstr_to_int» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$bitstr_to_int» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$int_to_bitstr» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$int_to_bitstr» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bits_to_int_signed» (arg0 : bits) (arg1 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$bits_to_int_signed» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$int_to_bits_unsigned» (arg0 : _root_.Nat) (arg1 : _root_.Int) (arg2 : bits) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bits, SpecTecCall.«$int_to_bits_unsigned» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$int_to_bits_signed» (arg0 : _root_.Nat) (arg1 : _root_.Int) (arg2 : bits) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bits, SpecTecCall.«$int_to_bits_signed» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$update_fieldValue» (arg0 : (_root_.List fieldValue)) (arg1 : nameIR) (arg2 : value) (arg3 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$update_fieldValue» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$invalidate_header» (arg0 : headerValue) (arg1 : headerValue) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨headerValue, SpecTecCall.«$invalidate_header» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$invalidate_headerUnion:case_1:pattern-iter:0» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$invalidate_headerUnion:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$invalidate_headerUnion:case_1:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$invalidate_headerUnion:case_1:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$write_bits_from_value:case_7:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_7:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$write_bits_from_value:case_8:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_8:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$write_bits_from_value:case_10:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_10:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:8» (arg0 : bound) (arg1 : (_root_.List typeParameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:8» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:8» (arg0 : bound) (arg1 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding:case_1:iter:8» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:serializable:pattern-iter:1» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Type_alpha:serializable:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Type_alpha:serializable:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List valueFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Type_alpha:serializable:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Type_alpha:non-default_2:iter:6» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List annotationList)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:non-default_2:iter:7» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:7» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:default_2:iter:6» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List annotationList)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:default_2:iter:7» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:7» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$shl» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$shl» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$shr» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$shr» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
