import SpecTecDecl0078

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

abbrev blockEvalLayer : Type := blockInstLayer


abbrev localEvalLayer : Type := localInstLayer


structure evalContext : Type where
  («GLOBAL» : globalEvalLayer)
  («BLOCK» : blockEvalLayer)
  («LOCAL» : localEvalLayer)
deriving _root_.DecidableEq


abbrev archState : Type := _root_.SpecTecExternTypes.archState


structure arch : Type where
  («STATE» : archState)
  («STORE» : store)
deriving _root_.DecidableEq


def «$find_objectState_e:case_1:downcast:1» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «$update_objectState_e:case_1:downcast:1» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


inductive continueEmptyResult : Type where
  | _EMPTY : continueEmptyResult
deriving _root_.DecidableEq


inductive continueResult (X : Type) : Type where
  | _CONT : X → (continueResult X)
deriving _root_.DecidableEq


inductive exitResult : Type where
  | EXIT : exitResult
deriving _root_.DecidableEq


inductive returnResult : Type where
  | RETURN : (_root_.Option value) → returnResult
deriving _root_.DecidableEq


inductive acceptTransitionResult : Type where
  | ACCEPT : acceptTransitionResult
deriving _root_.DecidableEq


inductive rejectTransitionResult : Type where
  | REJECT : errorValue → rejectTransitionResult
deriving _root_.DecidableEq


inductive stateTransitionResult : Type where
  | STATE : id → stateTransitionResult
deriving _root_.DecidableEq


inductive abortResult : Type where
  | EXIT : abortResult
  | REJECT : errorValue → abortResult
deriving _root_.DecidableEq


inductive expressionResult : Type where
  | _CONT : value → expressionResult
  | EXIT : expressionResult
  | REJECT : errorValue → expressionResult
deriving _root_.DecidableEq


def «Expr_eval:booleanLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option booleanLiteral) := match arg0 with | .TRUE => some (booleanLiteral.TRUE) | .FALSE => some (booleanLiteral.FALSE) | _ => none


def «Expr_eval:integerLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Expr_eval:stringLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «Expr_eval:referenceExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Expr_eval:defaultExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «Expr_eval:abort:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «Expr_eval:abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:cont:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «Expr_eval:cont:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:non-short-circuit-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:non-short-circuit-cont:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:land-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:land-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:land-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:land-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:lor-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none

end SpecTec
