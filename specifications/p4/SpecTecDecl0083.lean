import SpecTecDecl0082

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval:abort_4:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:tuple:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:array:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:headerStack:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:abort_5:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:cont-range:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:cont-offset:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Exprs_eval:cons-head-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Exprs_eval:cons-head-cont-tail-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Exprs_eval:cons-head-cont-tail-abort:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Exprs_eval:cons-head-cont-tail-cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Exprs_eval:cons-head-cont-tail-cont:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive keysetExpressionResult : Type where
  | _CONT : (_root_.List setValue) → keysetExpressionResult
  | EXIT : keysetExpressionResult
  | REJECT : errorValue → keysetExpressionResult
deriving _root_.DecidableEq


def «Argument_eval:typedExpressionIR:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


inductive storageReferenceResult : Type where
  | _CONT : (_root_.Option storageReference) → storageReferenceResult
  | EXIT : storageReferenceResult
  | REJECT : errorValue → storageReferenceResult
deriving _root_.DecidableEq


def «Argument_eval_lvalue:typedExpressionIR:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Lvalue_eval:referenceExpressionIR:downcast:0» (arg0 : lvalueIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Lvalue_eval:abort:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Lvalue_eval:stack-next-out-of-bounds:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:stack-next-out-of-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Lvalue_eval:stack-next-in-bounds:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:stack-next-in-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Lvalue_eval:stack-last-out-of-bounds:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:stack-last-out-of-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Lvalue_eval:stack-last-in-bounds:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:stack-last-in-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Lvalue_eval:cont:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:base-abort:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Lvalue_eval:base-cont-index-abort:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:base-cont-index-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Lvalue_eval:base-cont-index-cont:downcast:0» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Lvalue_eval:base-cont-index-cont:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none

end SpecTec
