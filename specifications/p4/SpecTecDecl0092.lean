import SpecTecDecl0091

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Call_eval:cont_2:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:cont_2:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Call_eval:cont-overflow_2:downcast:0» (arg0 : callee) : (_root_.Option builtinPopFrontMethodCallee) := match arg0 with | .BUILTIN_POP_FRONT field0 => some (builtinPopFrontMethodCallee.BUILTIN_POP_FRONT field0) | _ => none


def «Call_eval:cont-overflow_2:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Call_eval:cont-overflow_2:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:cont-overflow_2:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Call_eval:builtinIsValidMethodCallee-header:downcast:0» (arg0 : callee) : (_root_.Option builtinIsValidMethodCallee) := match arg0 with | .BUILTIN_IS_VALID field0 => some (builtinIsValidMethodCallee.BUILTIN_IS_VALID field0) | _ => none


def «Call_eval:builtinIsValidMethodCallee-header:downcast:1» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Call_eval:builtinSetValidMethodCallee:downcast:0» (arg0 : callee) : (_root_.Option builtinSetValidMethodCallee) := match arg0 with | .BUILTIN_SET_VALID field0 => some (builtinSetValidMethodCallee.BUILTIN_SET_VALID field0) | _ => none


def «Call_eval:builtinSetValidMethodCallee:downcast:1» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Call_eval:builtinSetInvalidMethodCallee:downcast:0» (arg0 : callee) : (_root_.Option builtinSetInvalidMethodCallee) := match arg0 with | .BUILTIN_SET_INVALID field0 => some (builtinSetInvalidMethodCallee.BUILTIN_SET_INVALID field0) | _ => none


def «Call_eval:builtinSetInvalidMethodCallee:downcast:1» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Call_eval:builtinIsValidMethodCallee-header-union:downcast:0» (arg0 : callee) : (_root_.Option builtinIsValidMethodCallee) := match arg0 with | .BUILTIN_IS_VALID field0 => some (builtinIsValidMethodCallee.BUILTIN_IS_VALID field0) | _ => none


def «Call_eval:builtinIsValidMethodCallee-header-union:downcast:1» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «Call_eval:builtinSizeMethodCallee:downcast:0» (arg0 : callee) : (_root_.Option builtinSizeMethodCallee) := match arg0 with | .BUILTIN_SIZE_OF field0 field1 => some (builtinSizeMethodCallee.BUILTIN_SIZE_OF field0 field1) | _ => none


def «Call_eval:copyin-abort-initializer:downcast:0» (arg0 : callee) : (_root_.Option externMethodCallee) := match arg0 with | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8 => some (externMethodCallee.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8) | _ => none


def «Call_eval:copyin-abort-initializer:downcast:5» (arg0 : copyInResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:copyin-cont-initializer:downcast:0» (arg0 : callee) : (_root_.Option externMethodCallee) := match arg0 with | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8 => some (externMethodCallee.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8) | _ => none


def «Call_eval:copyin-cont-initializer:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:copyin-abort:downcast:0» (arg0 : callee) : (_root_.Option externMethodCallee) := match arg0 with | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8 => some (externMethodCallee.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8) | _ => none


def «Call_eval:copyin-abort:downcast:5» (arg0 : copyInResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Call_eval:copyin-cont-non-abstract-reject:downcast:0» (arg0 : callee) : (_root_.Option externMethodCallee) := match arg0 with | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8 => some (externMethodCallee.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8) | _ => none


def «Call_eval:copyin-cont-non-abstract-reject:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:copyin-cont-non-abstract-reject:downcast:7» (arg0 : callResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «Call_eval:copyin-cont-non-abstract-non-reject:downcast:0» (arg0 : callee) : (_root_.Option externMethodCallee) := match arg0 with | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8 => some (externMethodCallee.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 field7 field8) | _ => none


def «Call_eval:copyin-cont-non-abstract-non-reject:downcast:5» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:copyin-reject:downcast:0» (arg0 : callee) : (_root_.Option parserApplyMethodCallee) := match arg0 with | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 => some (parserApplyMethodCallee.«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none


def «Call_eval:copyin-reject:downcast:3» (arg0 : copyInResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-reject:downcast:0» (arg0 : callee) : (_root_.Option parserApplyMethodCallee) := match arg0 with | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 => some (parserApplyMethodCallee.«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-reject:downcast:3» (arg0 : copyInResult) : (_root_.Option (continueResult (_root_.List (_root_.Option storageReference)))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-reject:downcast:4» (arg0 : parserStatementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «Call_eval:copyin-cont-parserLocalDeclarationListIR-cont-transition-reject:downcast:0» (arg0 : callee) : (_root_.Option parserApplyMethodCallee) := match arg0 with | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6 => some (parserApplyMethodCallee.«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none

end SpecTec
