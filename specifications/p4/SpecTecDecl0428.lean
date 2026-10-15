import SpecTecDecl0427

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_tableActionsPropertyIR» (arg0 : tableActionsPropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tableActionsPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableDefaultActionPropertyIR» (arg0 : tableDefaultActionPropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tableDefaultActionPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableEntriesPropertyIR» (arg0 : tableEntriesPropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tableEntriesPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tablePropertyIR» (arg0 : tablePropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tablePropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tablePropertyListIR:case_1:iter:0» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List tableProperty)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableProperty), SpecTecCall.«$lift_tablePropertyListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tablePropertyListIR» (arg0 : (_root_.List tablePropertyIR)) (arg1 : tablePropertyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tablePropertyList, SpecTecCall.«$lift_tablePropertyListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableDeclarationIR» (arg0 : tableDeclarationIR) (arg1 : tableDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableDeclaration, SpecTecCall.«$lift_tableDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlTypeDeclarationIR» (arg0 : controlTypeDeclarationIR) (arg1 : controlTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlTypeDeclaration, SpecTecCall.«$lift_controlTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlBodyIR» (arg0 : controlBodyIR) (arg1 : controlBody) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlBody, SpecTecCall.«$lift_controlBodyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlLocalDeclarationIR» (arg0 : controlLocalDeclarationIR) (arg1 : controlLocalDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlLocalDeclaration, SpecTecCall.«$lift_controlLocalDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlLocalDeclarationListIR:case_1:iter:0» (arg0 : (_root_.List controlLocalDeclarationIR)) (arg1 : (_root_.List controlLocalDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List controlLocalDeclaration), SpecTecCall.«$lift_controlLocalDeclarationListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlLocalDeclarationListIR» (arg0 : (_root_.List controlLocalDeclarationIR)) (arg1 : controlLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlLocalDeclarationList, SpecTecCall.«$lift_controlLocalDeclarationListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_controlDeclarationIR» (arg0 : controlDeclarationIR) (arg1 : controlDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlDeclaration, SpecTecCall.«$lift_controlDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_packageTypeDeclarationIR» (arg0 : packageTypeDeclarationIR) (arg1 : packageTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨packageTypeDeclaration, SpecTecCall.«$lift_packageTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_typeParameterList» (arg0 : typeParameterList) (arg1 : (_root_.List typeParameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeParameter), SpecTecCall.«$flatten_typeParameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_typeParameterListOpt» (arg0 : typeParameterListOpt) (arg1 : (_root_.List typeParameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeParameter), SpecTecCall.«$flatten_typeParameterListOpt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def TypeParameterListOpt_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeParameterListOpt) (arg3 : typingContext) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List typeId)), SpecTecCall.TypeParameterListOpt_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TypeParameterListOpt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TypeParameterListOpt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TypeParameterListOpt_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TypeParameterListOpt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TypeParameterListOpt_ok] unexpandRelationNotation
end Notation.TypeParameterListOpt_ok


noncomputable def «$lift_typedefIR» (arg0 : typedefIR) (arg1 : typedef) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedef, SpecTecCall.«$lift_typedefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typedefDeclarationIR» (arg0 : typedefDeclarationIR) (arg1 : typedefDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedefDeclaration, SpecTecCall.«$lift_typedefDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeDeclarationIR» (arg0 : typeDeclarationIR) (arg1 : typeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeDeclaration, SpecTecCall.«$lift_typeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_declarationIR» (arg0 : declarationIR) (arg1 : declaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨declaration, SpecTecCall.«$lift_declarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_p4programIR:case_1:iter:0» (arg0 : (_root_.List declarationIR)) (arg1 : (_root_.List declaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List declaration), SpecTecCall.«$lift_p4programIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_p4programIR» (arg0 : p4programIR) (arg1 : p4program) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨p4program, SpecTecCall.«$lift_p4programIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$un_lnot» (arg0 : value) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$un_lnot» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$largest_priority_wins» (arg0 : tableObjectProperty) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$largest_priority_wins» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$select_action» (arg0 : tableObjectProperty) (arg1 : (_root_.List tableMatch)) (arg2 : tableActionReferenceIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionReferenceIR, SpecTecCall.«$select_action» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_control_plane:case_3:iter:4» (arg0 : (_root_.List value)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$cast_control_plane:case_3:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_control_plane» (arg0 : evalContext) (arg1 : typedExpressionIR) (arg2 : typeIR) (arg3 : (_root_.Option typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typedExpressionIR), SpecTecCall.«$cast_control_plane» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_key» (arg0 : evalContext) (arg1 : (nameIR × (nameIR × typeIR))) (arg2 : tableKeysetInterface) (arg3 : simpleKeysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionIR, SpecTecCall.«$tableObject_create_entry_key» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_keys» (arg0 : evalContext) (arg1 : (_root_.List (nameIR × (nameIR × typeIR)))) (arg2 : tableKeysetInterface) (arg3 : (_root_.List simpleKeysetExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List simpleKeysetExpressionIR), SpecTecCall.«$tableObject_create_entry_keys» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_keyset» (arg0 : evalContext) (arg1 : tableKeysPropertyIR) (arg2 : tableKeysetInterface) (arg3 : keysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨keysetExpressionIR, SpecTecCall.«$tableObject_create_entry_keyset» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_1:iter:4» (arg0 : evalContext) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typedExpressionIR)) (arg3 : (_root_.List (_root_.Option typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typedExpressionIR)), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:4» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

end SpecTec
