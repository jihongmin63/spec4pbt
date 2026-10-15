import SpecTecDecl0073

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive parserObject : Type where
  | «PARSER `< % `> `( % `) `{ % % % `}» : theta → parameterListIR → frame → parserLocalDeclarationListIR → stateEnv → parserObject
deriving _root_.DecidableEq


inductive object : Type where
  | «EXTERN % `< % `> `{ % % % `}» : typeId → theta → objectState → frame → externMethodDefEnv → object
  | «PARSER `< % `> `( % `) `{ % % % `}» : theta → parameterListIR → frame → parserLocalDeclarationListIR → stateEnv → object
  | «CONTROL `< % `> `( % `) `{ % % % % `}» : theta → parameterListIR → frame → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → object
  | «PACKAGE `< % `> `{ % `}» : theta → frame → object
  | «TABLE % `{ % % `}» : typeId → frame → tableObjectProperty → object
  | «VALUE_SET `{ % `( % `) `}» : (_root_.List value) → _root_.Nat → object
deriving _root_.DecidableEq


abbrev callableDefEnv : Type := (map callableId callableDef)


abbrev constructorDefEnv : Type := (map callableId constructorDef)


abbrev store : Type := (map objectId object)


structure globalInstLayer : Type where
  («CONSTRUCTOR» : constructorDefEnv)
  («TYPE» : typeDefEnv)
  («CALLABLE» : callableDefEnv)
  («FRAME» : frame)
deriving _root_.DecidableEq


structure blockInstLayer : Type where
  («TYPE» : theta)
  («CALLABLE» : callableDefEnv)
  («STATE» : stateEnv)
  («FRAME» : frame)
deriving _root_.DecidableEq


structure localInstLayer : Type where
  («TYPE» : theta)
  («FRAMES» : (_root_.List frame))
deriving _root_.DecidableEq


structure instContext : Type where
  («PATH» : objectId)
  («GLOBAL» : globalInstLayer)
  («BLOCK» : blockInstLayer)
  («LOCAL» : localInstLayer)
deriving _root_.DecidableEq


def «Expr_inst:booleanLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option booleanLiteral) := match arg0 with | .TRUE => some (booleanLiteral.TRUE) | .FALSE => some (booleanLiteral.FALSE) | _ => none


def «Expr_inst:integerLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Expr_inst:stringLiteral:downcast:0» (arg0 : expressionIR) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «Expr_inst:referenceExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Expr_inst:defaultExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «Expr_inst:unaryExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «Expr_inst:non-short-circuit:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_inst:land-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_inst:land-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_inst:lor-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_inst:lor-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_inst:true:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_inst:false:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_inst:castExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «Expr_inst:invalidHeaderExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option invalidHeaderExpression) := match arg0 with | .«'{#}'» => some (invalidHeaderExpression.«'{#}'») | _ => none


def «Expr_inst:non-default:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_inst:default:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_inst:non-default_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_inst:default_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_inst:errorAccessExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option errorAccessExpressionIR) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpressionIR.«ERROR '.' %» field0) | _ => none


def «Expr_inst:enum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_inst:enum:downcast:4» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «Expr_inst:serenum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none

end SpecTec
