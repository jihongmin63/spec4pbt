import SpecTecDecl0063

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Decl_ok:packageTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option packageTypeDeclaration) := match arg0 with | .«% PACKAGE % % `( % `) ';'» field0 field1 field2 field3 => some (packageTypeDeclaration.«% PACKAGE % % `( % `) ';'» field0 field1 field2 field3) | _ => none


inductive actctxt : Type where
  | ACTION : actctxt
  | NOACTION : actctxt
deriving _root_.DecidableEq


def «Call_convention_arg_ok:typedExpression:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$is_static_callableTypeIR:case_1:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «$is_static_callableTypeIR:case_2:downcast:0» (arg0 : callableTypeIR) : (_root_.Option builtinSizeMethodTypeIR) := match arg0 with | .BUILTIN_SIZE_OF => some (builtinSizeMethodTypeIR.BUILTIN_SIZE_OF) | _ => none


def «$is_static_assert_callableTypeIR:case_1:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableTarget_ok:prefixedNonTypeName:downcast:0» (arg0 : expression) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «CallableTarget_ok:memberAccessExpression-prefixedTypeName:downcast:0» (arg0 : expression) : (_root_.Option memberAccessExpression) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpression.«% '.' %» field0 field1) | _ => none


def «CallableTarget_ok:memberAccessExpression-prefixedTypeName:downcast:1» (arg0 : memberAccessBase) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «CallableTarget_ok:memberAccessExpression-expression:downcast:0» (arg0 : expression) : (_root_.Option memberAccessExpression) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpression.«% '.' %» field0 field1) | _ => none


def «CallableTarget_ok:memberAccessExpression-expression:downcast:1» (arg0 : memberAccessBase) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «CallableTarget_ok:parenthesizedExpression:downcast:0» (arg0 : expression) : (_root_.Option parenthesizedExpression) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpression.«`( % `)» field0) | _ => none


def «CallableType_ok:actionTypeIR:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «CallableType_ok:actionTypeIR:downcast:2» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «CallableType_ok:functionTypeIR:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «CallableType_ok:functionTypeIR:downcast:2» (arg0 : callableTypeDefIR) : (_root_.Option functionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (functionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (functionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «CallableType_ok:functionTypeIR:downcast:4:0» (arg0 : callableTypeIR) : (_root_.Option functionTypeIR) := match arg0 with | .«FUNCTION % `( % `) ':' %» field0 field1 field2 => some (functionTypeIR.«FUNCTION % `( % `) ':' %» field0 field1 field2) | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (functionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_ok:builtinMethodTypeIR-header-stack-push-front:downcast:2» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «CallableType_ok:builtinMethodTypeIR-header-stack-pop-front:downcast:2» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «CallableType_ok:isValid:downcast:2» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «CallableType_ok:setValid:downcast:2» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «CallableType_ok:setInvalid:downcast:2» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «CallableType_ok:isValid_2:downcast:2» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «CallableType_ok:externMethodTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «CallableType_ok:externMethodTypeIR:downcast:10:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_ok:parserApplyMethodTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none


def «CallableType_ok:controlApplyMethodTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «CallableType_ok:tableApplyMethodTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «Call_ok:actionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «Call_ok:definedFunctionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option definedFunctionTypeIR) := match arg0 with | .«FUNCTION % `( % `) ':' %» field0 field1 field2 => some (definedFunctionTypeIR.«FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «Call_ok:externFunctionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «Call_ok:builtinMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option builtinMethodTypeIR) := match arg0 with | .BUILTIN_IS_VALID => some (builtinMethodTypeIR.BUILTIN_IS_VALID) | .BUILTIN_SET_VALID => some (builtinMethodTypeIR.BUILTIN_SET_VALID) | .BUILTIN_SET_INVALID => some (builtinMethodTypeIR.BUILTIN_SET_INVALID) | .BUILTIN_PUSH_FRONT => some (builtinMethodTypeIR.BUILTIN_PUSH_FRONT) | .BUILTIN_POP_FRONT => some (builtinMethodTypeIR.BUILTIN_POP_FRONT) | .BUILTIN_SIZE_OF => some (builtinMethodTypeIR.BUILTIN_SIZE_OF) | _ => none

end SpecTec
