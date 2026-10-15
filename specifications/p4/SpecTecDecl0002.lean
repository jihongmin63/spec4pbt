import SpecTecDecl0001

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$flatten_namedExpressionList:case_1:downcast:0» (arg0 : namedExpressionList) : (_root_.Option namedExpression) := match arg0 with | .«% '=' %» field0 field1 => some (namedExpression.«% '=' %» field0 field1) | _ => none


inductive unaryExpression : Type where
  | «% %» : unop → expression → unaryExpression
deriving _root_.DecidableEq


inductive binaryExpression : Type where
  | «% % %» : expression → binop → expression → binaryExpression
deriving _root_.DecidableEq


inductive ternaryExpression : Type where
  | «% '?' % ':' %» : expression → expression → expression → ternaryExpression
deriving _root_.DecidableEq


inductive castExpression : Type where
  | «`( % `) %» : type → expression → castExpression
deriving _root_.DecidableEq


inductive sequenceOrRecordExpression : Type where
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → sequenceOrRecordExpression
deriving _root_.DecidableEq


inductive dataExpression : Type where
  | «'{#}'» : dataExpression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → dataExpression
deriving _root_.DecidableEq


inductive memberAccessExpression : Type where
  | «% '.' %» : memberAccessBase → member → memberAccessExpression
deriving _root_.DecidableEq


inductive indexAccessExpression : Type where
  | «% `[ % `]» : expression → expression → indexAccessExpression
deriving _root_.DecidableEq


inductive sliceAccessExpression : Type where
  | «% `[ % % % `]» : expression → expression → sliceop → expression → sliceAccessExpression
deriving _root_.DecidableEq


inductive accessExpression : Type where
  | «ERROR '.' %» : member → accessExpression
  | «% '.' %» : memberAccessBase → member → accessExpression
  | «% `[ % `]» : expression → expression → accessExpression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → accessExpression
deriving _root_.DecidableEq


inductive callExpression : Type where
  | «% `( % `)» : callTarget → argumentList → callExpression
  | «% `< % `> `( % `)» : callableTarget → realTypeArgumentList → argumentList → callExpression
deriving _root_.DecidableEq


inductive parenthesizedExpression : Type where
  | «`( % `)» : expression → parenthesizedExpression
deriving _root_.DecidableEq


def «$flatten_expressionList:case_2:downcast:0» (arg0 : expressionList) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


abbrev sequenceElementExpression : Type := expressionList


inductive recordElementExpression : Type where
  | «% '=' %» : name → expression → recordElementExpression
  | «% '=' % ',' '...'» : name → expression → recordElementExpression
  | «% '=' % ',' %» : name → expression → namedExpressionList → recordElementExpression
  | «% '=' % ',' % ',' '...'» : name → expression → namedExpressionList → recordElementExpression
deriving _root_.DecidableEq


abbrev constructorTarget : Type := namedType


mutual

inductive expressionNonBrace : Type where
  | TRUE : expressionNonBrace
  | FALSE : expressionNonBrace
  | D : _root_.Int → expressionNonBrace
  | «% W %» : _root_.Nat → _root_.Int → expressionNonBrace
  | «% S %» : _root_.Nat → _root_.Int → expressionNonBrace
  | «'"' % '"'» : _root_.String → expressionNonBrace
  | _ID : _root_.String → expressionNonBrace
  | APPLY : expressionNonBrace
  | KEY : expressionNonBrace
  | ACTIONS : expressionNonBrace
  | STATE : expressionNonBrace
  | ENTRIES : expressionNonBrace
  | TYPE : expressionNonBrace
  | PRIORITY : expressionNonBrace
  | «_ID '.' %» : nonTypeName → expressionNonBrace
  | THIS : expressionNonBrace
  | «% %» : unop → expression → expressionNonBrace
  | «% % %» : expressionNonBrace → binop → expression → expressionNonBrace
  | «% '?' % ':' %» : expressionNonBrace → expression → expression → expressionNonBrace
  | «`( % `) %» : type → expression → expressionNonBrace
  | «ERROR '.' %» : member → expressionNonBrace
  | «% '.' %» : memberAccessBaseNonBrace → member → expressionNonBrace
  | «% `[ % `]» : expressionNonBrace → expression → expressionNonBrace
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → expressionNonBrace
  | «% `( % `)» : callTargetNonBrace → argumentList → expressionNonBrace
  | «% `< % `> `( % `)» : expressionNonBrace → realTypeArgumentList → argumentList → expressionNonBrace
  | «`( % `)» : expression → expressionNonBrace
deriving _root_.DecidableEq

inductive memberAccessBaseNonBrace : Type where
  | _TID : _root_.String → memberAccessBaseNonBrace
  | «_TID '.' %» : typeName → memberAccessBaseNonBrace
  | TRUE : memberAccessBaseNonBrace
  | FALSE : memberAccessBaseNonBrace
  | D : _root_.Int → memberAccessBaseNonBrace
  | «% W %» : _root_.Nat → _root_.Int → memberAccessBaseNonBrace
  | «% S %» : _root_.Nat → _root_.Int → memberAccessBaseNonBrace
  | «'"' % '"'» : _root_.String → memberAccessBaseNonBrace
  | _ID : _root_.String → memberAccessBaseNonBrace
  | APPLY : memberAccessBaseNonBrace
  | KEY : memberAccessBaseNonBrace
  | ACTIONS : memberAccessBaseNonBrace
  | STATE : memberAccessBaseNonBrace
  | ENTRIES : memberAccessBaseNonBrace
  | TYPE : memberAccessBaseNonBrace
  | PRIORITY : memberAccessBaseNonBrace
  | «_ID '.' %» : nonTypeName → memberAccessBaseNonBrace
  | THIS : memberAccessBaseNonBrace
  | «% %» : unop → expression → memberAccessBaseNonBrace
  | «% % %» : expressionNonBrace → binop → expression → memberAccessBaseNonBrace
  | «% '?' % ':' %» : expressionNonBrace → expression → expression → memberAccessBaseNonBrace
  | «`( % `) %» : type → expression → memberAccessBaseNonBrace
  | «ERROR '.' %» : member → memberAccessBaseNonBrace
  | «% '.' %» : memberAccessBaseNonBrace → member → memberAccessBaseNonBrace
  | «% `[ % `]» : expressionNonBrace → expression → memberAccessBaseNonBrace
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → memberAccessBaseNonBrace
  | «% `( % `)» : callTargetNonBrace → argumentList → memberAccessBaseNonBrace
  | «% `< % `> `( % `)» : expressionNonBrace → realTypeArgumentList → argumentList → memberAccessBaseNonBrace
  | «`( % `)» : expression → memberAccessBaseNonBrace
deriving _root_.DecidableEq

inductive callTargetNonBrace : Type where
  | TRUE : callTargetNonBrace
  | FALSE : callTargetNonBrace
  | D : _root_.Int → callTargetNonBrace
  | «% W %» : _root_.Nat → _root_.Int → callTargetNonBrace
  | «% S %» : _root_.Nat → _root_.Int → callTargetNonBrace
  | «'"' % '"'» : _root_.String → callTargetNonBrace
  | _ID : _root_.String → callTargetNonBrace
  | APPLY : callTargetNonBrace
  | KEY : callTargetNonBrace
  | ACTIONS : callTargetNonBrace
  | STATE : callTargetNonBrace
  | ENTRIES : callTargetNonBrace
  | TYPE : callTargetNonBrace
  | PRIORITY : callTargetNonBrace
  | «_ID '.' %» : nonTypeName → callTargetNonBrace
  | THIS : callTargetNonBrace
  | «% %» : unop → expression → callTargetNonBrace
  | «% % %» : expressionNonBrace → binop → expression → callTargetNonBrace
  | «% '?' % ':' %» : expressionNonBrace → expression → expression → callTargetNonBrace
  | «`( % `) %» : type → expression → callTargetNonBrace
  | «ERROR '.' %» : member → callTargetNonBrace
  | «% '.' %» : memberAccessBaseNonBrace → member → callTargetNonBrace
  | «% `[ % `]» : expressionNonBrace → expression → callTargetNonBrace
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → callTargetNonBrace
  | «% `( % `)» : callTargetNonBrace → argumentList → callTargetNonBrace
  | «% `< % `> `( % `)» : expressionNonBrace → realTypeArgumentList → argumentList → callTargetNonBrace
  | «`( % `)» : expression → callTargetNonBrace
  | _TID : _root_.String → callTargetNonBrace
  | «_TID '.' %» : typeName → callTargetNonBrace
  | «% `< % `>» : prefixedTypeName → typeArgumentList → callTargetNonBrace
deriving _root_.DecidableEq

end


abbrev callableTargetNonBrace : Type := expressionNonBrace


inductive binaryExpressionNonBrace : Type where
  | «% % %» : expressionNonBrace → binop → expression → binaryExpressionNonBrace
deriving _root_.DecidableEq


inductive ternaryExpressionNonBrace : Type where
  | «% '?' % ':' %» : expressionNonBrace → expression → expression → ternaryExpressionNonBrace
deriving _root_.DecidableEq


inductive memberAccessExpressionNonBrace : Type where
  | «% '.' %» : memberAccessBaseNonBrace → member → memberAccessExpressionNonBrace
deriving _root_.DecidableEq


inductive indexAccessExpressionNonBrace : Type where
  | «% `[ % `]» : expressionNonBrace → expression → indexAccessExpressionNonBrace
deriving _root_.DecidableEq


inductive sliceAccessExpressionNonBrace : Type where
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → sliceAccessExpressionNonBrace
deriving _root_.DecidableEq


inductive accessExpressionNonBrace : Type where
  | «ERROR '.' %» : member → accessExpressionNonBrace
  | «% '.' %» : memberAccessBaseNonBrace → member → accessExpressionNonBrace
  | «% `[ % `]» : expressionNonBrace → expression → accessExpressionNonBrace
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → accessExpressionNonBrace
deriving _root_.DecidableEq


inductive callExpressionNonBrace : Type where
  | «% `( % `)» : callTargetNonBrace → argumentList → callExpressionNonBrace
  | «% `< % `> `( % `)» : callableTargetNonBrace → realTypeArgumentList → argumentList → callExpressionNonBrace
deriving _root_.DecidableEq


def «$expressionNonBrace_as_expression:case_1:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option literalExpression) := match arg0 with | .TRUE => some (literalExpression.TRUE) | .FALSE => some (literalExpression.FALSE) | .D field0 => some (literalExpression.D field0) | .«% W %» field0 field1 => some (literalExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (literalExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (literalExpression.«'"' % '"'» field0) | _ => none


def «$expressionNonBrace_as_expression:case_2:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option referenceExpression) := match arg0 with | ._ID field0 => some (referenceExpression._ID field0) | .APPLY => some (referenceExpression.APPLY) | .KEY => some (referenceExpression.KEY) | .ACTIONS => some (referenceExpression.ACTIONS) | .STATE => some (referenceExpression.STATE) | .ENTRIES => some (referenceExpression.ENTRIES) | .TYPE => some (referenceExpression.TYPE) | .PRIORITY => some (referenceExpression.PRIORITY) | .«_ID '.' %» field0 => some (referenceExpression.«_ID '.' %» field0) | .THIS => some (referenceExpression.THIS) | _ => none


def «$expressionNonBrace_as_expression:case_3:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option unaryExpression) := match arg0 with | .«% %» field0 field1 => some (unaryExpression.«% %» field0 field1) | _ => none


def «$expressionNonBrace_as_expression:case_4:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option binaryExpressionNonBrace) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionNonBrace.«% % %» field0 field1 field2) | _ => none


def «$expressionNonBrace_as_expression:case_5:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option ternaryExpressionNonBrace) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionNonBrace.«% '?' % ':' %» field0 field1 field2) | _ => none


def «$expressionNonBrace_as_expression:case_6:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option castExpression) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpression.«`( % `) %» field0 field1) | _ => none

end SpecTec
