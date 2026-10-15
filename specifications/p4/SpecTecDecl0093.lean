import SpecTecDecl0092

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Call_eval:copyin-cont-parserLocalDeclarationListIR-cont-transition-reject:downcast:3» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-cont-transition-reject:downcast:4» (arg0 : parserStatementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-cont-transition-reject:downcast:5» (arg0 : transitionResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «Call_eval:parserLocalDeclarationListIR-cont-transition-accept:downcast:0» (arg0 : callee) : (_root_.Option parserApplyMethodCallee) := match arg0 with | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 => some (parserApplyMethodCallee.«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none


def «Call_eval:parserLocalDeclarationListIR-cont-transition-accept:downcast:3» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:parserLocalDeclarationListIR-cont-transition-accept:downcast:4» (arg0 : parserStatementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «Call_eval:parserLocalDeclarationListIR-cont-transition-accept:downcast:5» (arg0 : transitionResult) : (_root_.Option acceptTransitionResult) := match arg0 with | .ACCEPT => some (acceptTransitionResult.ACCEPT) | _ => none


def «Call_eval:controlApplyMethodCallee-copyin-exit:downcast:0» (arg0 : callee) : (_root_.Option controlApplyMethodCallee) := match arg0 with | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlApplyMethodCallee.«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Call_eval:controlApplyMethodCallee-copyin-exit:downcast:7» (arg0 : copyInResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Call_eval:controlApplyMethodCallee-localDecl-exit:downcast:0» (arg0 : callee) : (_root_.Option controlApplyMethodCallee) := match arg0 with | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlApplyMethodCallee.«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Call_eval:controlApplyMethodCallee-localDecl-exit:downcast:7» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:controlApplyMethodCallee-localDecl-exit:downcast:8» (arg0 : controlLocalDeclarationResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:downcast:0» (arg0 : callee) : (_root_.Option controlApplyMethodCallee) := match arg0 with | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlApplyMethodCallee.«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:downcast:7» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:downcast:8» (arg0 : controlLocalDeclarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:downcast:9» (arg0 : controlBodyResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Call_eval:controlApplyMethodCallee-cont:downcast:0» (arg0 : callee) : (_root_.Option controlApplyMethodCallee) := match arg0 with | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlApplyMethodCallee.«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Call_eval:controlApplyMethodCallee-cont:downcast:7» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:controlApplyMethodCallee-cont:downcast:8» (arg0 : controlLocalDeclarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «Call_eval:tableApplyMethodCallee-exit:downcast:0» (arg0 : callee) : (_root_.Option tableApplyMethodCallee) := match arg0 with | .«TABLE % '.' APPLY `{ % ';' % `}» field0 field1 field2 => some (tableApplyMethodCallee.«TABLE % '.' APPLY `{ % ';' % `}» field0 field1 field2) | _ => none


def «Call_eval:tableApplyMethodCallee-exit:downcast:2» (arg0 : tableResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Call_eval:tableApplyMethodCallee-return:downcast:0» (arg0 : callee) : (_root_.Option tableApplyMethodCallee) := match arg0 with | .«TABLE % '.' APPLY `{ % ';' % `}» field0 field1 field2 => some (tableApplyMethodCallee.«TABLE % '.' APPLY `{ % ';' % `}» field0 field1 field2) | _ => none


def «Call_eval:tableApplyMethodCallee-return:downcast:2» (arg0 : tableResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


inductive simpleKeysetExpressionResult : Type where
  | _CONT : setValue → simpleKeysetExpressionResult
  | EXIT : simpleKeysetExpressionResult
  | REJECT : errorValue → simpleKeysetExpressionResult
deriving _root_.DecidableEq


def «Eval_keyset_simple:abort:downcast:0» (arg0 : simpleKeysetExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Eval_keyset_simple:abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keyset_simple:cont-setValue:downcast:0» (arg0 : simpleKeysetExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Eval_keyset_simple:cont-setValue:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:cont-setValue:downcast:2» (arg0 : value) : (_root_.Option setValue) := match arg0 with | .«SET `{ % `}» field0 => some (setValue.«SET `{ % `}» field0) | .«SET `{ % `( % `) `}» field0 field1 => some (setValue.«SET `{ % `( % `) `}» field0 field1) | .«SET `{ % '&&&' % `}» field0 field1 => some (setValue.«SET `{ % '&&&' % `}» field0 field1) | .«SET `{ % '..' % `}» field0 field1 => some (setValue.«SET `{ % '..' % `}» field0 field1) | .«SET `{ '...' `}» => some (setValue.«SET `{ '...' `}») | _ => none


def «Eval_keyset_simple:cont-objectReferenceValue:downcast:0» (arg0 : simpleKeysetExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Eval_keyset_simple:cont-objectReferenceValue:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:cont-objectReferenceValue:downcast:2» (arg0 : value) : (_root_.Option objectReferenceValue) := match arg0 with | .REF field0 => some (objectReferenceValue.REF field0) | _ => none

end SpecTec
