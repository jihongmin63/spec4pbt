import SpecTecDecl0032

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

abbrev referenceExpressionIR : Type := prefixedNameIR


abbrev defaultExpressionIR : Type := defaultExpression


inductive unaryExpressionIR : Type where
  | «% %» : unop → typedExpressionIR → unaryExpressionIR
deriving _root_.DecidableEq


inductive binaryExpressionIR : Type where
  | «% % %» : typedExpressionIR → binop → typedExpressionIR → binaryExpressionIR
deriving _root_.DecidableEq


inductive ternaryExpressionIR : Type where
  | «% '?' % ':' %» : typedExpressionIR → typedExpressionIR → typedExpressionIR → ternaryExpressionIR
deriving _root_.DecidableEq


inductive castExpressionIR : Type where
  | «`( % `) %» : typeIR → typedExpressionIR → castExpressionIR
deriving _root_.DecidableEq


abbrev invalidHeaderExpressionIR : Type := invalidHeaderExpression


inductive sequenceExpressionIR : Type where
  | «SEQ `{ % `}» : typedExpressionListIR → sequenceExpressionIR
  | «SEQ `{ % ',' '...' `}» : typedExpressionListIR → sequenceExpressionIR
deriving _root_.DecidableEq


inductive recordExpressionIR : Type where
  | «RECORD `{ % `}» : namedExpressionListIR → recordExpressionIR
  | «RECORD `{ % ',' '...' `}» : namedExpressionListIR → recordExpressionIR
deriving _root_.DecidableEq


inductive dataExpressionIR : Type where
  | «'{#}'» : dataExpressionIR
  | «SEQ `{ % `}» : typedExpressionListIR → dataExpressionIR
  | «SEQ `{ % ',' '...' `}» : typedExpressionListIR → dataExpressionIR
  | «RECORD `{ % `}» : namedExpressionListIR → dataExpressionIR
  | «RECORD `{ % ',' '...' `}» : namedExpressionListIR → dataExpressionIR
deriving _root_.DecidableEq


inductive errorAccessExpressionIR : Type where
  | «ERROR '.' %» : nameIR → errorAccessExpressionIR
deriving _root_.DecidableEq


inductive memberAccessExpressionIR : Type where
  | «% '.' %» : memberAccessBaseIR → nameIR → memberAccessExpressionIR
deriving _root_.DecidableEq


inductive indexAccessExpressionIR : Type where
  | «% `[ % `]» : typedExpressionIR → typedExpressionIR → indexAccessExpressionIR
deriving _root_.DecidableEq


inductive sliceAccessExpressionIR : Type where
  | «% `[ % % % `]» : typedExpressionIR → typedExpressionIR → sliceop → typedExpressionIR → sliceAccessExpressionIR
deriving _root_.DecidableEq


inductive accessExpressionIR : Type where
  | «ERROR '.' %» : nameIR → accessExpressionIR
  | «% '.' %» : memberAccessBaseIR → nameIR → accessExpressionIR
  | «% `[ % `]» : typedExpressionIR → typedExpressionIR → accessExpressionIR
  | «% `[ % % % `]» : typedExpressionIR → typedExpressionIR → sliceop → typedExpressionIR → accessExpressionIR
deriving _root_.DecidableEq


inductive callExpressionIR : Type where
  | «% `( % `)» : constructorTargetIR → argumentListIR → callExpressionIR
  | «% `< % `> `( % `)» : callableTargetIR → typeArgumentListIR → argumentListIR → callExpressionIR
deriving _root_.DecidableEq


inductive parenthesizedExpressionIR : Type where
  | «`( % `)» : typedExpressionIR → parenthesizedExpressionIR
deriving _root_.DecidableEq


inductive simpleKeysetExpressionIR : Type where
  | «% '#' %» : expressionIR → expressionNoteIR → simpleKeysetExpressionIR
  | «% '&&&' %» : typedExpressionIR → typedExpressionIR → simpleKeysetExpressionIR
  | «% '..' %» : typedExpressionIR → typedExpressionIR → simpleKeysetExpressionIR
  | DEFAULT : simpleKeysetExpressionIR
  | «'_'» : simpleKeysetExpressionIR
deriving _root_.DecidableEq


abbrev simpleKeysetExpressionListIR : Type := (_root_.List simpleKeysetExpressionIR)


inductive tupleKeysetExpressionIR : Type where
  | «`( % `)» : simpleKeysetExpressionListIR → tupleKeysetExpressionIR
deriving _root_.DecidableEq


inductive keysetExpressionIR : Type where
  | «% '#' %» : expressionIR → expressionNoteIR → keysetExpressionIR
  | «% '&&&' %» : typedExpressionIR → typedExpressionIR → keysetExpressionIR
  | «% '..' %» : typedExpressionIR → typedExpressionIR → keysetExpressionIR
  | DEFAULT : keysetExpressionIR
  | «'_'» : keysetExpressionIR
  | «`( % `)» : simpleKeysetExpressionListIR → keysetExpressionIR
deriving _root_.DecidableEq


def «$flatten_keysetExpressionIR:case_1:downcast:0» (arg0 : keysetExpressionIR) : (_root_.Option simpleKeysetExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (simpleKeysetExpressionIR.«% '#' %» field0 field1) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpressionIR.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpressionIR.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpressionIR.DEFAULT) | .«'_'» => some (simpleKeysetExpressionIR.«'_'») | _ => none


def «$flatten_keysetExpressionIR:case_2:downcast:0» (arg0 : keysetExpressionIR) : (_root_.Option tupleKeysetExpressionIR) := match arg0 with | .«`( % `)» field0 => some (tupleKeysetExpressionIR.«`( % `)» field0) | _ => none


inductive lvalueNoteIR : Type where
  | «`( % `)» : typeIR → lvalueNoteIR
deriving _root_.DecidableEq


mutual

inductive lvalueIR : Type where
  | _BARE : nameIR → lvalueIR
  | «'.' %» : nameIR → lvalueIR
  | «% '.' %» : typedLvalueIR → nameIR → lvalueIR
  | «% `[ % `]» : typedLvalueIR → typedExpressionIR → lvalueIR
  | «% `[ % % % `]» : typedLvalueIR → typedExpressionIR → sliceop → typedExpressionIR → lvalueIR
  | «`( % `)» : typedLvalueIR → lvalueIR
deriving _root_.DecidableEq

inductive typedLvalueIR : Type where
  | «% '#' %» : lvalueIR → lvalueNoteIR → typedLvalueIR
deriving _root_.DecidableEq

end


def «$typedLvalueIR_as_typedExpressionIR:case_1:downcast:0» (arg0 : lvalueIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_1:downcast:0» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_2:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_2:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_3:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_4:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$typedExpressionIR_as_typedLvalueIR:case_5:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none

end SpecTec
