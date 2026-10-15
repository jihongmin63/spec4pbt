import SpecTecDecl0038

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$lift_dataTypeIR:case_5:downcast:0» (arg0 : dataTypeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$lift_dataTypeIR:case_6:downcast:0» (arg0 : dataTypeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_typeIR_as_typeOrVoid:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option voidTypeIR) := match arg0 with | .VOID => some (voidTypeIR.VOID) | _ => none


def «$lift_parameterIR:case_1:downcast:0:0» (arg0 : parameterInitializerIR) : (_root_.Option constantInitializerIR) := match arg0 with | .«'=' _VALUE %» field0 => some (constantInitializerIR.«'=' _VALUE %» field0) | _ => none


def «$lift_dataExpressionIR:case_1:downcast:0» (arg0 : dataExpressionIR) : (_root_.Option invalidHeaderExpression) := match arg0 with | .«'{#}'» => some (invalidHeaderExpression.«'{#}'») | _ => none


def «$lift_dataExpressionIR:case_2:downcast:0» (arg0 : dataExpressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «$lift_dataExpressionIR:case_3:downcast:0» (arg0 : dataExpressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «$lift_dataExpressionIR:case_4:downcast:0» (arg0 : dataExpressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$lift_dataExpressionIR:case_5:downcast:0» (arg0 : dataExpressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$lift_memberAccessBaseIR:case_2:downcast:0» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$lift_accessExpressionIR:case_1:downcast:0» (arg0 : accessExpressionIR) : (_root_.Option errorAccessExpressionIR) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpressionIR.«ERROR '.' %» field0) | _ => none


def «$lift_accessExpressionIR:case_2:downcast:0» (arg0 : accessExpressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «$lift_accessExpressionIR:case_3:downcast:0» (arg0 : accessExpressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «$lift_accessExpressionIR:case_4:downcast:0» (arg0 : accessExpressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$lift_callableTargetIR_as_expression:case_2:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_callableTargetIR_as_expression:case_3:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_expressionIR:case_1:downcast:0» (arg0 : expressionIR) : (_root_.Option literalExpression) := match arg0 with | .TRUE => some (literalExpression.TRUE) | .FALSE => some (literalExpression.FALSE) | .D field0 => some (literalExpression.D field0) | .«% W %» field0 field1 => some (literalExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (literalExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (literalExpression.«'"' % '"'» field0) | _ => none


def «$lift_expressionIR:case_2:downcast:0» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_expressionIR:case_3:downcast:0» (arg0 : expressionIR) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «$lift_expressionIR:case_4:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «$lift_expressionIR:case_5:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «$lift_expressionIR:case_6:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «$lift_expressionIR:case_7:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «$lift_expressionIR:case_8:downcast:0» (arg0 : expressionIR) : (_root_.Option dataExpressionIR) := match arg0 with | .«'{#}'» => some (dataExpressionIR.«'{#}'») | .«SEQ `{ % `}» field0 => some (dataExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (dataExpressionIR.«SEQ `{ % ',' '...' `}» field0) | .«RECORD `{ % `}» field0 => some (dataExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (dataExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$lift_expressionIR:case_9:downcast:0» (arg0 : expressionIR) : (_root_.Option accessExpressionIR) := match arg0 with | .«ERROR '.' %» field0 => some (accessExpressionIR.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (accessExpressionIR.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (accessExpressionIR.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (accessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$lift_expressionIR:case_10:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$lift_expressionIR:case_11:downcast:0» (arg0 : expressionIR) : (_root_.Option parenthesizedExpressionIR) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpressionIR.«`( % `)» field0) | _ => none


def «$lift_simpleKeysetExpressionIR:case_1:downcast:0» (arg0 : simpleKeysetExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$lift_keysetExpressionIR:case_1:downcast:0» (arg0 : keysetExpressionIR) : (_root_.Option simpleKeysetExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (simpleKeysetExpressionIR.«% '#' %» field0 field1) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpressionIR.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpressionIR.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpressionIR.DEFAULT) | .«'_'» => some (simpleKeysetExpressionIR.«'_'») | _ => none


def «$lift_keysetExpressionIR:case_2:downcast:0» (arg0 : keysetExpressionIR) : (_root_.Option tupleKeysetExpressionIR) := match arg0 with | .«`( % `)» field0 => some (tupleKeysetExpressionIR.«`( % `)» field0) | _ => none


def «$lift_typeArgumentIR_as_realTypeArgument:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option voidTypeIR) := match arg0 with | .VOID => some (voidTypeIR.VOID) | _ => none


def «$lift_argumentIR:case_1:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none

end SpecTec
