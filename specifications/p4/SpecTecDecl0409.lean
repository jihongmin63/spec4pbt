import SpecTecDecl0408

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$flatten_objectDeclarationList» (arg0 : objectDeclarationList) (arg1 : (_root_.List objectDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List objectDeclaration), SpecTecCall.«$flatten_objectDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_p4program» (arg0 : p4program) (arg1 : (_root_.List declaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List declaration), SpecTecCall.«$flatten_p4program» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_parserBlockElementStatementList» (arg0 : parserBlockElementStatementList) (arg1 : (_root_.List parserBlockElementStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserBlockElementStatement), SpecTecCall.«$flatten_parserBlockElementStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_parserLocalDeclarationList» (arg0 : parserLocalDeclarationList) (arg1 : (_root_.List parserLocalDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserLocalDeclaration), SpecTecCall.«$flatten_parserLocalDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_prefixedNameIR» (arg0 : prefixedNameIR) (arg1 : nameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameIR, SpecTecCall.«$flatten_prefixedNameIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_prefixedNameIR_as_prefixedNonTypeName» (arg0 : prefixedNameIR) (arg1 : prefixedNonTypeName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨prefixedNonTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedNonTypeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_prefixedNameIR_as_prefixedTypeName» (arg0 : prefixedNameIR) (arg1 : prefixedTypeName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨prefixedTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedTypeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_referenceExpressionIR» (arg0 : referenceExpressionIR) (arg1 : referenceExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨referenceExpression, SpecTecCall.«$lift_referenceExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_var_t» (arg0 : prefixedNameIR) (arg1 : cursor) (arg2 : typingContext) (arg3 : (_root_.Option varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_var_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_var_value_t» (arg0 : prefixedNameIR) (arg1 : cursor) (arg2 : typingContext) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$find_var_value_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_typeDef_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : prefixedNameIR) (arg3 : (_root_.Option typeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typeDefIR), SpecTecCall.«$find_typeDef_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_callableDef_non_overloaded_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : prefixedNameIR) (arg3 : (_root_.Option (callableId × callableTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callableId × callableTypeDefIR)), SpecTecCall.«$find_callableDef_non_overloaded_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «TableType_ok:rule:iter:3» (arg0 : (_root_.List prefixedNameIR)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«TableType_ok:rule:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_callableDef_non_overload_i» (arg0 : cursor) (arg1 : instContext) (arg2 : prefixedNameIR) (arg3 : (_root_.Option (cursor × (callableId × callableDef)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (cursor × (callableId × callableDef))), SpecTecCall.«$find_callableDef_non_overload_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_var_i» (arg0 : prefixedNameIR) (arg1 : cursor) (arg2 : instContext) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$find_var_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_typeDef_i» (arg0 : cursor) (arg1 : instContext) (arg2 : prefixedNameIR) (arg3 : (_root_.Option typeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typeDefIR), SpecTecCall.«$find_typeDef_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_var_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : prefixedNameIR) (arg3 : value) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$add_var_e» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_vars_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : (_root_.List prefixedNameIR)) (arg3 : (_root_.List value)) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$add_vars_e» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$update_var_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : prefixedNameIR) (arg3 : value) (arg4 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$update_var_e» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$find_var_e» (arg0 : prefixedNameIR) (arg1 : cursor) (arg2 : evalContext) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$find_var_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_typeDef_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : prefixedNameIR) (arg3 : (_root_.Option typeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typeDefIR), SpecTecCall.«$find_typeDef_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def ConstDecl_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : constantDeclarationIR) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.ConstDecl_eval arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ConstDecl_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ConstDecl_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ConstDecl_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ConstDecl_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ConstDecl_eval] unexpandRelationNotation
end Notation.ConstDecl_eval


noncomputable def «$find_tableActionIR_qualified» (arg0 : (_root_.List tableActionIR)) (arg1 : nameIR) (arg2 : (_root_.Option (nameIR × tableActionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_qualified» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_tableActionIR_unqualified'» (arg0 : (_root_.List tableActionIR)) (arg1 : nameIR) (arg2 : (_root_.Option (nameIR × tableActionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_unqualified'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_tableActionIR_unqualified» (arg0 : (_root_.List tableActionIR)) (arg1 : nameIR) (arg2 : (_root_.Option (nameIR × tableActionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_unqualified» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$flatten_selectCaseList» (arg0 : selectCaseList) (arg1 : (_root_.List selectCase)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List selectCase), SpecTecCall.«$flatten_selectCaseList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$switchLabelIR_of_switchCaseIR» (arg0 : switchCaseIR) (arg1 : switchLabelIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchLabelIR, SpecTecCall.«$switchLabelIR_of_switchCaseIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Stmt_ok:table:iter:4» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List switchLabelIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List switchLabelIR), SpecTecCall.«Stmt_ok:table:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Stmt_ok:general:iter:3» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List switchLabelIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List switchLabelIR), SpecTecCall.«Stmt_ok:general:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_non_fallthrough_switchCaseIR» (arg0 : switchCaseIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_non_fallthrough_switchCaseIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match:iter:1» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
