import SpecTecDecl0090

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Call_eval:copyin-exit:downcast:3» (arg0 : copyInResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Call_eval:copyin-cont-ActionBody-exit:downcast:0» (arg0 : callee) : (_root_.Option actionCallee) := match arg0 with | .«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4 => some (actionCallee.«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:copyin-cont-ActionBody-exit:downcast:3» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:return:downcast:0» (arg0 : callee) : (_root_.Option actionCallee) := match arg0 with | .«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4 => some (actionCallee.«ACTION % '.' % `( % '#' % `) %» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:return:downcast:3» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:definedFunctionCallee-copyin-abort:downcast:0» (arg0 : callee) : (_root_.Option definedFunctionCallee) := match arg0 with | .«FUNCTION % `< % `> `( % '#' % `) %» field0 field1 field2 field3 field4 => some (definedFunctionCallee.«FUNCTION % `< % `> `( % '#' % `) %» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:definedFunctionCallee-copyin-abort:downcast:5» (arg0 : copyInResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:definedFunctionCallee-cont:downcast:0» (arg0 : callee) : (_root_.Option definedFunctionCallee) := match arg0 with | .«FUNCTION % `< % `> `( % '#' % `) %» field0 field1 field2 field3 field4 => some (definedFunctionCallee.«FUNCTION % `< % `> `( % '#' % `) %» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:definedFunctionCallee-cont:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:externFunctionCallee-copyin-abort:downcast:0» (arg0 : callee) : (_root_.Option externFunctionCallee) := match arg0 with | .«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4 => some (externFunctionCallee.«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:externFunctionCallee-copyin-abort:downcast:5» (arg0 : copyInResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:externFunctionCallee-copyin-cont-call-reject:downcast:0» (arg0 : callee) : (_root_.Option externFunctionCallee) := match arg0 with | .«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4 => some (externFunctionCallee.«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:externFunctionCallee-copyin-cont-call-reject:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:externFunctionCallee-copyin-cont-call-reject:downcast:7» (arg0 : callResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:downcast:0» (arg0 : callee) : (_root_.Option externFunctionCallee) := match arg0 with | .«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4 => some (externFunctionCallee.«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» field0 field1 field2 field3 field4) | _ => none


def «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:abort:downcast:0» (arg0 : callee) : (_root_.Option builtinPushFrontMethodCallee) := match arg0 with | .BUILTIN_PUSH_FRONT field0 => some (builtinPushFrontMethodCallee.BUILTIN_PUSH_FRONT field0) | _ => none


def «Call_eval:abort:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Call_eval:abort:downcast:2» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:cont:downcast:0» (arg0 : callee) : (_root_.Option builtinPushFrontMethodCallee) := match arg0 with | .BUILTIN_PUSH_FRONT field0 => some (builtinPushFrontMethodCallee.BUILTIN_PUSH_FRONT field0) | _ => none


def «Call_eval:cont:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Call_eval:cont:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:cont:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Call_eval:cont-overflow:downcast:0» (arg0 : callee) : (_root_.Option builtinPushFrontMethodCallee) := match arg0 with | .BUILTIN_PUSH_FRONT field0 => some (builtinPushFrontMethodCallee.BUILTIN_PUSH_FRONT field0) | _ => none


def «Call_eval:cont-overflow:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Call_eval:cont-overflow:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:cont-overflow:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Call_eval:abort_2:downcast:0» (arg0 : callee) : (_root_.Option builtinPopFrontMethodCallee) := match arg0 with | .BUILTIN_POP_FRONT field0 => some (builtinPopFrontMethodCallee.BUILTIN_POP_FRONT field0) | _ => none


def «Call_eval:abort_2:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Call_eval:abort_2:downcast:2» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:cont_2:downcast:0» (arg0 : callee) : (_root_.Option builtinPopFrontMethodCallee) := match arg0 with | .BUILTIN_POP_FRONT field0 => some (builtinPopFrontMethodCallee.BUILTIN_POP_FRONT field0) | _ => none


def «Call_eval:cont_2:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none

end SpecTec
