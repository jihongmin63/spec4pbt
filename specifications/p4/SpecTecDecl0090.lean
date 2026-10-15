import SpecTecDecl0089

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Callee_eval:cont_5:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:abort_6:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_7:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:cont_7:downcast:2» (arg0 : value) : (_root_.Option objectReferenceValue) := match arg0 with | .REF field0 => some (objectReferenceValue.REF field0) | _ => none


def «Callee_eval:cont_7:downcast:4» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «Callee_eval:abort_7:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_8:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:cont_8:downcast:2» (arg0 : value) : (_root_.Option objectReferenceValue) := match arg0 with | .REF field0 => some (objectReferenceValue.REF field0) | _ => none


def «Callee_eval:cont_8:downcast:4» (arg0 : object) : (_root_.Option parserObject) := match arg0 with | .«PARSER `< % `> `( % `) `{ % % % `}» field0 field1 field2 field3 field4 => some (parserObject.«PARSER `< % `> `( % `) `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «Callee_eval:abort_8:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_9:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:cont_9:downcast:2» (arg0 : value) : (_root_.Option objectReferenceValue) := match arg0 with | .REF field0 => some (objectReferenceValue.REF field0) | _ => none


def «Callee_eval:cont_9:downcast:4» (arg0 : object) : (_root_.Option controlObject) := match arg0 with | .«CONTROL `< % `> `( % `) `{ % % % % `}» field0 field1 field2 field3 field4 field5 => some (controlObject.«CONTROL `< % `> `( % `) `{ % % % % `}» field0 field1 field2 field3 field4 field5) | _ => none


def «Callee_eval:abort_9:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_10:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:cont_10:downcast:2» (arg0 : value) : (_root_.Option objectReferenceValue) := match arg0 with | .REF field0 => some (objectReferenceValue.REF field0) | _ => none


def «Callee_eval:cont_10:downcast:4» (arg0 : object) : (_root_.Option tableObject) := match arg0 with | .«TABLE % `{ % % `}» field0 field1 field2 => some (tableObject.«TABLE % `{ % % `}» field0 field1 field2) | _ => none


inductive copyInArgumentResult : Type where
  | _CONT : (_root_.Option storageReference) → copyInArgumentResult
  | EXIT : copyInArgumentResult
  | REJECT : errorValue → copyInArgumentResult
deriving _root_.DecidableEq


def «Copy_in_arg:abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Copy_in_arg:cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Copy_in_arg:abort_2:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Copy_in_arg:cont_2:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Copy_in_arg:abort_3:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Copy_in_arg:cont_3:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive copyInResult : Type where
  | _CONT : (_root_.List (_root_.Option storageReference)) → copyInResult
  | EXIT : copyInResult
  | REJECT : errorValue → copyInResult
deriving _root_.DecidableEq


def «Copy_in:cons-head-abort:downcast:0» (arg0 : copyInArgumentResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Copy_in:cons-head-cont-tail-abort:downcast:0» (arg0 : copyInArgumentResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Copy_in:cons-head-cont-tail-abort:downcast:1» (arg0 : copyInResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Copy_in:cons-head-cont-tail-cont:downcast:0» (arg0 : copyInArgumentResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Copy_in:cons-head-cont-tail-cont:downcast:1» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Copy_in_default:rule:downcast:5» (arg0 : parameterInitializerIR) : (_root_.Option constantInitializerIR) := match arg0 with | .«'=' _VALUE %» field0 => some (constantInitializerIR.«'=' _VALUE %» field0) | _ => none


def «Call_eval:copyin-exit:downcast:0» (arg0 : callee) : (_root_.Option actionCallee) := match arg0 with | .«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4 => some (actionCallee.«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4) | _ => none

end SpecTec
