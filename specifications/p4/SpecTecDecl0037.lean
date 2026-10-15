import SpecTecDecl0036

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive p4programIR : Type where
  | «% ';'» : (_root_.List declarationIR) → p4programIR
deriving _root_.DecidableEq


inductive callAlign : Type where
  | «GIVEN % DEFAULT % OPTIONAL %» : (_root_.List parameterIR) → (_root_.List parameterIR) → (_root_.List parameterIR) → callAlign
deriving _root_.DecidableEq


def «$align_parameterListIR_given:case_2:downcast:2» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


inductive callTargetKey : Type where
  | «% `( % `)» : nameIR → (_root_.List (_root_.Option id)) → callTargetKey
deriving _root_.DecidableEq


inductive namedCallTargetKey : Type where
  | «% `( % `)» : nameIR → (_root_.List id) → namedCallTargetKey
deriving _root_.DecidableEq


inductive unnamedCallTargetKey : Type where
  | «% `( % `)» : nameIR → _root_.Nat → unnamedCallTargetKey
deriving _root_.DecidableEq


inductive callTargetParameter : Type where
  | «% '#' % '#' %» : nameIR → _root_.Bool → _root_.Bool → callTargetParameter
deriving _root_.DecidableEq


abbrev callTargetValue : Type := (_root_.List callTargetParameter)


inductive callTargetMatch : Type where
  | MATCH : (_root_.List id) → (_root_.List id) → callTargetMatch
  | NOMATCH : callTargetMatch
deriving _root_.DecidableEq


inductive callResolution (V : Type) : Type where
  | «% ':' % '#' % '#' %» : callableId → V → (_root_.List nameIR) → (_root_.List nameIR) → (callResolution V)
deriving _root_.DecidableEq


def «$callTargetKey':case_1:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$find_name_annotation_opt:case_2:downcast:0» (arg0 : annotationList) : (_root_.Option annotation) := match arg0 with | .«'@' %» field0 => some (annotation.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotation.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotation.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotation.«'@' PRAGMA % %» field0 field1) | _ => none


def «$find_name_annotation_opt:case_3:downcast:0» (arg0 : annotationList) : (_root_.Option annotation) := match arg0 with | .«'@' %» field0 => some (annotation.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotation.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotation.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotation.«'@' PRAGMA % %» field0 field1) | _ => none


def «$find_name_annotation_opt:case_4:downcast:0» (arg0 : annotationList) : (_root_.Option annotationListNonEmpty) := match arg0 with | .«'@' %» field0 => some (annotationListNonEmpty.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotationListNonEmpty.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotationListNonEmpty.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotationListNonEmpty.«'@' PRAGMA % %» field0 field1) | .«% %» field0 field1 => some (annotationListNonEmpty.«% %» field0 field1) | _ => none


def «$find_name_annotation_opt:case_5:downcast:0» (arg0 : annotationList) : (_root_.Option annotationListNonEmpty) := match arg0 with | .«'@' %» field0 => some (annotationListNonEmpty.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotationListNonEmpty.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotationListNonEmpty.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotationListNonEmpty.«'@' PRAGMA % %» field0 field1) | .«% %» field0 field1 => some (annotationListNonEmpty.«% %» field0 field1) | _ => none


def «$add_annotationList:case_3:downcast:0» (arg0 : annotationList) : (_root_.Option annotationListNonEmpty) := match arg0 with | .«'@' %» field0 => some (annotationListNonEmpty.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotationListNonEmpty.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotationListNonEmpty.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotationListNonEmpty.«'@' PRAGMA % %» field0 field1) | .«% %» field0 field1 => some (annotationListNonEmpty.«% %» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_1:downcast:0» (arg0 : expressionIR) : (_root_.Option unaryExpressionIR) := match arg0 with | .«% %» field0 field1 => some (unaryExpressionIR.«% %» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_2:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «$subexpressions_of_expressionIR:case_3:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «$subexpressions_of_expressionIR:case_4:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_5:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «$subexpressions_of_expressionIR:case_6:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «$subexpressions_of_expressionIR:case_7:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$subexpressions_of_expressionIR:case_8:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$subexpressions_of_expressionIR:case_9:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_9:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_10:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «$subexpressions_of_expressionIR:case_11:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$subexpressions_of_expressionIR:case_12:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$subexpressions_of_expressionIR:case_13:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$subexpressions_of_expressionIR:case_14:downcast:0» (arg0 : expressionIR) : (_root_.Option parenthesizedExpressionIR) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpressionIR.«`( % `)» field0) | _ => none


def «$subexpressions_of_argumentIR:case_1:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none

end SpecTec
