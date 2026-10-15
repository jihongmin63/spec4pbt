import SpecTecDecl0050

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_constructor_package:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_constructor_package:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$definable_constructor:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$definable_constructor:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | _ => 1


def «$definable_constructor:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$definable_constructor:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$definable_constructor:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$definable_constructor:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «Expr_eval_lctk:booleanLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option booleanLiteral) := match arg0 with | .TRUE => some (booleanLiteral.TRUE) | .FALSE => some (booleanLiteral.FALSE) | _ => none


def «Expr_eval_lctk:integerLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Expr_eval_lctk:stringLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «Expr_eval_lctk:referenceExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Expr_eval_lctk:defaultExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «Expr_eval_lctk:unaryExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «Expr_eval_lctk:non-short-circuit:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:land-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:land-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:lor-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:lor-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:true:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:false:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_eval_lctk:castExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «Expr_eval_lctk:invalidHeaderExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option invalidHeaderExpression) := match arg0 with | .«'{#}'» => some (invalidHeaderExpression.«'{#}'») | _ => none


def «Expr_eval_lctk:non-default:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval_lctk:default:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval_lctk:non-default_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval_lctk:default_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval_lctk:errorAccessExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option errorAccessExpressionIR) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpressionIR.«ERROR '.' %» field0) | _ => none


def «Expr_eval_lctk:enum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:enum:downcast:5» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «Expr_eval_lctk:serenum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval_lctk:serenum:downcast:5» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none

end SpecTec
