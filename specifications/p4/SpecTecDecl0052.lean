import SpecTecDecl0051

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval_lctk:header-stack-size:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:header-stack-size:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval_lctk:header-stack-size:downcast:4» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Expr_eval_lctk:struct:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:struct:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval_lctk:struct:downcast:2» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «Expr_eval_lctk:header:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:header:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval_lctk:header:downcast:2» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Expr_eval_lctk:header-union:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:header-union:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval_lctk:header-union:downcast:2» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «Expr_eval_lctk:tuple:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval_lctk:tuple:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:tuple:downcast:2» (arg0 : value) : (_root_.Option tupleValue) := match arg0 with | .«TUPLE `( % `)» field0 => some (tupleValue.«TUPLE `( % `)» field0) | _ => none


def «Expr_eval_lctk:array:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval_lctk:array:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:array:downcast:2» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «Expr_eval_lctk:stack:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval_lctk:stack:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:stack:downcast:2» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Expr_eval_lctk:range:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «Expr_eval_lctk:offset:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «Expr_eval_lctk:static_assert:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval_lctk:static_assert:downcast:1» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Expr_eval_lctk:static_assert:downcast:2» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:static_assert:downcast:3» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «Expr_eval_lctk:static_assert:downcast:11» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «Expr_eval_lctk:size-expression:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval_lctk:size-type-monomorphic:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval_lctk:size-type-polymorphic:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval_lctk:callExpressionIR-parenthesized:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none

end SpecTec
