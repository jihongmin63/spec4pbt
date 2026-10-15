import SpecTecDecl0413

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$PSA_setup_clone_i2e_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_clone_i2e_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_clone_e2e_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_clone_e2e_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_resubmit_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_resubmit_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_recirculate_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_recirculate_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_hdr_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_hdr_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_ingress_user_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_ingress_user_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_hdr_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_hdr_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_egress_user_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_egress_user_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Copy_in_default:rule:iter:3» (arg0 : (_root_.List parameterInitializerIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def Copy_in_default (arg0 : parameterListIR) (arg1 : cursor) (arg2 : evalContext) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Copy_in_default arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Copy_in_default
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_default arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Copy_in_default.relationNotation
        #[x0, Lean.mkAtom "@", x1, x2, Lean.mkAtom "~>", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg " @ " term:arg ppSpace colGt term:51 " ~> " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_default.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_default] unexpandRelationNotation
end Notation.Copy_in_default


noncomputable def «$flatten_parameterList» (arg0 : parameterList) (arg1 : (_root_.List parameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameter), SpecTecCall.«$flatten_parameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_constructorParameterListOpt» (arg0 : constructorParameterListOpt) (arg1 : (_root_.List constructorParameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorParameter), SpecTecCall.«$flatten_constructorParameterListOpt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callableId'» (arg0 : parameterList) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«$callableId'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callableId» (arg0 : name) (arg1 : parameterList) (arg2 : callableId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableId, SpecTecCall.«$callableId» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$constructorId» (arg0 : name) (arg1 : constructorParameterListOpt) (arg2 : constructorId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorId, SpecTecCall.«$constructorId» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callableId_of_externMethodPrototype» (arg0 : externMethodPrototype) (arg1 : callableId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableId, SpecTecCall.«$callableId_of_externMethodPrototype» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$constructorId_of_externConstructorPrototype» (arg0 : externConstructorPrototype) (arg1 : constructorId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorId, SpecTecCall.«$constructorId_of_externConstructorPrototype» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:4» (arg0 : (_root_.List externMethodPrototype)) (arg1 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:14» (arg0 : (_root_.List externConstructorPrototype)) (arg1 : (_root_.List constructorId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorId), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:14» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_parserStateList» (arg0 : parserStateList) (arg1 : (_root_.List parserState)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserState), SpecTecCall.«$flatten_parserStateList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$prefixedNonTypeName» (arg0 : prefixedNonTypeName) (arg1 : prefixedNameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨prefixedNameIR, SpecTecCall.«$prefixedNonTypeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$prefixedTypeName» (arg0 : prefixedTypeName) (arg1 : prefixedNameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨prefixedNameIR, SpecTecCall.«$prefixedTypeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_realTypeArgumentList» (arg0 : realTypeArgumentList) (arg1 : (_root_.List realTypeArgument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List realTypeArgument), SpecTecCall.«$flatten_realTypeArgumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_singleton_list_expression» (arg0 : expression) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_singleton_list_expression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_simpleKeysetExpressionList» (arg0 : simpleKeysetExpressionList) (arg1 : (_root_.List simpleKeysetExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List simpleKeysetExpression), SpecTecCall.«$flatten_simpleKeysetExpressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def SwitchLabel_table_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : switchLabel) (arg3 : switchLabelIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchLabelIR, SpecTecCall.SwitchLabel_table_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.SwitchLabel_table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchLabel_table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.SwitchLabel_table_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchLabel_table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchLabel_table_ok] unexpandRelationNotation
end Notation.SwitchLabel_table_ok


noncomputable def «$match_switchLabelIR_table» (arg0 : id) (arg1 : switchLabelIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def SwitchCases_table_eval (arg0 : id) (arg1 : switchCaseListIR) (arg2 : (_root_.Option blockStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option blockStatementIR), SpecTecCall.SwitchCases_table_eval arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.SwitchCases_table_eval
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.SwitchCases_table_eval x0 x1 x2
end Notation.SwitchCases_table_eval


noncomputable def «$insert_NoAction_tablePropertyIR» (arg0 : tableContext) (arg1 : (_root_.List tablePropertyIR)) (arg2 : (tableContext × (_root_.List tablePropertyIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × (_root_.List tablePropertyIR)), SpecTecCall.«$insert_NoAction_tablePropertyIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$init_table:case_1:iter:1» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_table:case_1:iter:10» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_table:case_1:iter:5» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
