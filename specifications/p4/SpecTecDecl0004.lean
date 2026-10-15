import SpecTecDecl0003

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$expression_as_expressionNonBrace:case_15:downcast:0» (arg0 : expression) : (_root_.Option parenthesizedExpression) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpression.«`( % `)» field0) | _ => none


inductive simpleKeysetExpression : Type where
  | TRUE : simpleKeysetExpression
  | FALSE : simpleKeysetExpression
  | D : _root_.Int → simpleKeysetExpression
  | «% W %» : _root_.Nat → _root_.Int → simpleKeysetExpression
  | «% S %» : _root_.Nat → _root_.Int → simpleKeysetExpression
  | «'"' % '"'» : _root_.String → simpleKeysetExpression
  | _ID : _root_.String → simpleKeysetExpression
  | APPLY : simpleKeysetExpression
  | KEY : simpleKeysetExpression
  | ACTIONS : simpleKeysetExpression
  | STATE : simpleKeysetExpression
  | ENTRIES : simpleKeysetExpression
  | TYPE : simpleKeysetExpression
  | PRIORITY : simpleKeysetExpression
  | «_ID '.' %» : nonTypeName → simpleKeysetExpression
  | THIS : simpleKeysetExpression
  | «'...'» : simpleKeysetExpression
  | «% %» : unop → expression → simpleKeysetExpression
  | «% % %» : expression → binop → expression → simpleKeysetExpression
  | «% '?' % ':' %» : expression → expression → expression → simpleKeysetExpression
  | «`( % `) %» : type → expression → simpleKeysetExpression
  | «'{#}'» : simpleKeysetExpression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → simpleKeysetExpression
  | «ERROR '.' %» : member → simpleKeysetExpression
  | «% '.' %» : memberAccessBase → member → simpleKeysetExpression
  | «% `[ % `]» : expression → expression → simpleKeysetExpression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → simpleKeysetExpression
  | «% `( % `)» : callTarget → argumentList → simpleKeysetExpression
  | «% `< % `> `( % `)» : callableTarget → realTypeArgumentList → argumentList → simpleKeysetExpression
  | «`( % `)» : expression → simpleKeysetExpression
  | «% '&&&' %» : expression → expression → simpleKeysetExpression
  | «% '..' %» : expression → expression → simpleKeysetExpression
  | DEFAULT : simpleKeysetExpression
  | «'_'» : simpleKeysetExpression
deriving _root_.DecidableEq


inductive simpleKeysetExpressionList : Type where
  | TRUE : simpleKeysetExpressionList
  | FALSE : simpleKeysetExpressionList
  | D : _root_.Int → simpleKeysetExpressionList
  | «% W %» : _root_.Nat → _root_.Int → simpleKeysetExpressionList
  | «% S %» : _root_.Nat → _root_.Int → simpleKeysetExpressionList
  | «'"' % '"'» : _root_.String → simpleKeysetExpressionList
  | _ID : _root_.String → simpleKeysetExpressionList
  | APPLY : simpleKeysetExpressionList
  | KEY : simpleKeysetExpressionList
  | ACTIONS : simpleKeysetExpressionList
  | STATE : simpleKeysetExpressionList
  | ENTRIES : simpleKeysetExpressionList
  | TYPE : simpleKeysetExpressionList
  | PRIORITY : simpleKeysetExpressionList
  | «_ID '.' %» : nonTypeName → simpleKeysetExpressionList
  | THIS : simpleKeysetExpressionList
  | «'...'» : simpleKeysetExpressionList
  | «% %» : unop → expression → simpleKeysetExpressionList
  | «% % %» : expression → binop → expression → simpleKeysetExpressionList
  | «% '?' % ':' %» : expression → expression → expression → simpleKeysetExpressionList
  | «`( % `) %» : type → expression → simpleKeysetExpressionList
  | «'{#}'» : simpleKeysetExpressionList
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → simpleKeysetExpressionList
  | «ERROR '.' %» : member → simpleKeysetExpressionList
  | «% '.' %» : memberAccessBase → member → simpleKeysetExpressionList
  | «% `[ % `]» : expression → expression → simpleKeysetExpressionList
  | «% `[ % % % `]» : expression → expression → sliceop → expression → simpleKeysetExpressionList
  | «% `( % `)» : callTarget → argumentList → simpleKeysetExpressionList
  | «% `< % `> `( % `)» : callableTarget → realTypeArgumentList → argumentList → simpleKeysetExpressionList
  | «`( % `)» : expression → simpleKeysetExpressionList
  | «% '&&&' %» : expression → expression → simpleKeysetExpressionList
  | «% '..' %» : expression → expression → simpleKeysetExpressionList
  | DEFAULT : simpleKeysetExpressionList
  | «'_'» : simpleKeysetExpressionList
  | «% ',' %» : simpleKeysetExpressionList → simpleKeysetExpression → simpleKeysetExpressionList
deriving _root_.DecidableEq


def «$flatten_simpleKeysetExpressionList:case_1:downcast:0» (arg0 : simpleKeysetExpressionList) : (_root_.Option simpleKeysetExpression) := match arg0 with | .TRUE => some (simpleKeysetExpression.TRUE) | .FALSE => some (simpleKeysetExpression.FALSE) | .D field0 => some (simpleKeysetExpression.D field0) | .«% W %» field0 field1 => some (simpleKeysetExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (simpleKeysetExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (simpleKeysetExpression.«'"' % '"'» field0) | ._ID field0 => some (simpleKeysetExpression._ID field0) | .APPLY => some (simpleKeysetExpression.APPLY) | .KEY => some (simpleKeysetExpression.KEY) | .ACTIONS => some (simpleKeysetExpression.ACTIONS) | .STATE => some (simpleKeysetExpression.STATE) | .ENTRIES => some (simpleKeysetExpression.ENTRIES) | .TYPE => some (simpleKeysetExpression.TYPE) | .PRIORITY => some (simpleKeysetExpression.PRIORITY) | .«_ID '.' %» field0 => some (simpleKeysetExpression.«_ID '.' %» field0) | .THIS => some (simpleKeysetExpression.THIS) | .«'...'» => some (simpleKeysetExpression.«'...'») | .«% %» field0 field1 => some (simpleKeysetExpression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (simpleKeysetExpression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (simpleKeysetExpression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (simpleKeysetExpression.«`( % `) %» field0 field1) | .«'{#}'» => some (simpleKeysetExpression.«'{#}'») | .«`{ % % `}» field0 field1 => some (simpleKeysetExpression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (simpleKeysetExpression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (simpleKeysetExpression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (simpleKeysetExpression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (simpleKeysetExpression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (simpleKeysetExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (simpleKeysetExpression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (simpleKeysetExpression.«`( % `)» field0) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpression.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpression.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpression.DEFAULT) | .«'_'» => some (simpleKeysetExpression.«'_'») | _ => none


inductive tupleKeysetExpression : Type where
  | «`( % '&&&' % `)» : expression → expression → tupleKeysetExpression
  | «`( % '..' % `)» : expression → expression → tupleKeysetExpression
  | «`( DEFAULT `)» : tupleKeysetExpression
  | «`( '_' `)» : tupleKeysetExpression
  | «`( % ',' % `)» : simpleKeysetExpression → simpleKeysetExpressionList → tupleKeysetExpression
deriving _root_.DecidableEq


inductive keysetExpression : Type where
  | TRUE : keysetExpression
  | FALSE : keysetExpression
  | D : _root_.Int → keysetExpression
  | «% W %» : _root_.Nat → _root_.Int → keysetExpression
  | «% S %» : _root_.Nat → _root_.Int → keysetExpression
  | «'"' % '"'» : _root_.String → keysetExpression
  | _ID : _root_.String → keysetExpression
  | APPLY : keysetExpression
  | KEY : keysetExpression
  | ACTIONS : keysetExpression
  | STATE : keysetExpression
  | ENTRIES : keysetExpression
  | TYPE : keysetExpression
  | PRIORITY : keysetExpression
  | «_ID '.' %» : nonTypeName → keysetExpression
  | THIS : keysetExpression
  | «'...'» : keysetExpression
  | «% %» : unop → expression → keysetExpression
  | «% % %» : expression → binop → expression → keysetExpression
  | «% '?' % ':' %» : expression → expression → expression → keysetExpression
  | «`( % `) %» : type → expression → keysetExpression
  | «'{#}'» : keysetExpression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → keysetExpression
  | «ERROR '.' %» : member → keysetExpression
  | «% '.' %» : memberAccessBase → member → keysetExpression
  | «% `[ % `]» : expression → expression → keysetExpression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → keysetExpression
  | «% `( % `)» : callTarget → argumentList → keysetExpression
  | «% `< % `> `( % `)» : callableTarget → realTypeArgumentList → argumentList → keysetExpression
  | «`( % `)» : expression → keysetExpression
  | «% '&&&' %» : expression → expression → keysetExpression
  | «% '..' %» : expression → expression → keysetExpression
  | DEFAULT : keysetExpression
  | «'_'» : keysetExpression
  | «`( % '&&&' % `)» : expression → expression → keysetExpression
  | «`( % '..' % `)» : expression → expression → keysetExpression
  | «`( DEFAULT `)» : keysetExpression
  | «`( '_' `)» : keysetExpression
  | «`( % ',' % `)» : simpleKeysetExpression → simpleKeysetExpressionList → keysetExpression
deriving _root_.DecidableEq


def «$flatten_realTypeArgumentList:case_1:downcast:0» (arg0 : realTypeArgumentList) : (_root_.Option realTypeArgument) := match arg0 with | .BOOL => some (realTypeArgument.BOOL) | .ERROR => some (realTypeArgument.ERROR) | .MATCH_KIND => some (realTypeArgument.MATCH_KIND) | .STRING => some (realTypeArgument.STRING) | .INT => some (realTypeArgument.INT) | .«INT `< % `>» field0 => some (realTypeArgument.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (realTypeArgument.«INT `< `( % `) `>» field0) | .BIT => some (realTypeArgument.BIT) | .«BIT `< % `>» field0 => some (realTypeArgument.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (realTypeArgument.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (realTypeArgument.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (realTypeArgument.«VARBIT `< `( % `) `>» field0) | ._TID field0 => some (realTypeArgument._TID field0) | .«_TID '.' %» field0 => some (realTypeArgument.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (realTypeArgument.«% `< % `>» field0 field1) | .«% `[ % `]» field0 field1 => some (realTypeArgument.«% `[ % `]» field0 field1) | .«LIST `< % `>» field0 => some (realTypeArgument.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (realTypeArgument.«TUPLE `< % `>» field0) | .VOID => some (realTypeArgument.VOID) | .«'_'» => some (realTypeArgument.«'_'») | _ => none


def «$flatten_typeArgumentList:case_2:downcast:0» (arg0 : typeArgumentList) : (_root_.Option typeArgument) := match arg0 with | .BOOL => some (typeArgument.BOOL) | .ERROR => some (typeArgument.ERROR) | .MATCH_KIND => some (typeArgument.MATCH_KIND) | .STRING => some (typeArgument.STRING) | .INT => some (typeArgument.INT) | .«INT `< % `>» field0 => some (typeArgument.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (typeArgument.«INT `< `( % `) `>» field0) | .BIT => some (typeArgument.BIT) | .«BIT `< % `>» field0 => some (typeArgument.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (typeArgument.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (typeArgument.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (typeArgument.«VARBIT `< `( % `) `>» field0) | ._TID field0 => some (typeArgument._TID field0) | .«_TID '.' %» field0 => some (typeArgument.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (typeArgument.«% `< % `>» field0 field1) | .«% `[ % `]» field0 field1 => some (typeArgument.«% `[ % `]» field0 field1) | .«LIST `< % `>» field0 => some (typeArgument.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (typeArgument.«TUPLE `< % `>» field0) | .VOID => some (typeArgument.VOID) | .«'_'» => some (typeArgument.«'_'») | ._ID field0 => some (typeArgument._ID field0) | .APPLY => some (typeArgument.APPLY) | .KEY => some (typeArgument.KEY) | .ACTIONS => some (typeArgument.ACTIONS) | .STATE => some (typeArgument.STATE) | .ENTRIES => some (typeArgument.ENTRIES) | .TYPE => some (typeArgument.TYPE) | .PRIORITY => some (typeArgument.PRIORITY) | _ => none


def «$flatten_argumentList:case_2:downcast:0» (arg0 : argumentList) : (_root_.Option argument) := match arg0 with | .TRUE => some (argument.TRUE) | .FALSE => some (argument.FALSE) | .D field0 => some (argument.D field0) | .«% W %» field0 field1 => some (argument.«% W %» field0 field1) | .«% S %» field0 field1 => some (argument.«% S %» field0 field1) | .«'"' % '"'» field0 => some (argument.«'"' % '"'» field0) | ._ID field0 => some (argument._ID field0) | .APPLY => some (argument.APPLY) | .KEY => some (argument.KEY) | .ACTIONS => some (argument.ACTIONS) | .STATE => some (argument.STATE) | .ENTRIES => some (argument.ENTRIES) | .TYPE => some (argument.TYPE) | .PRIORITY => some (argument.PRIORITY) | .«_ID '.' %» field0 => some (argument.«_ID '.' %» field0) | .THIS => some (argument.THIS) | .«'...'» => some (argument.«'...'») | .«% %» field0 field1 => some (argument.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (argument.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (argument.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (argument.«`( % `) %» field0 field1) | .«'{#}'» => some (argument.«'{#}'») | .«`{ % % `}» field0 field1 => some (argument.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (argument.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (argument.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (argument.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (argument.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (argument.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (argument.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (argument.«`( % `)» field0) | .«% '=' %» field0 field1 => some (argument.«% '=' %» field0 field1) | .«% '=' '_'» field0 => some (argument.«% '=' '_'» field0) | .«'_'» => some (argument.«'_'») | _ => none


def «$flatten_argumentList:case_3:downcast:0» (arg0 : argumentList) : (_root_.Option argumentListNonEmpty) := match arg0 with | .TRUE => some (argumentListNonEmpty.TRUE) | .FALSE => some (argumentListNonEmpty.FALSE) | .D field0 => some (argumentListNonEmpty.D field0) | .«% W %» field0 field1 => some (argumentListNonEmpty.«% W %» field0 field1) | .«% S %» field0 field1 => some (argumentListNonEmpty.«% S %» field0 field1) | .«'"' % '"'» field0 => some (argumentListNonEmpty.«'"' % '"'» field0) | ._ID field0 => some (argumentListNonEmpty._ID field0) | .APPLY => some (argumentListNonEmpty.APPLY) | .KEY => some (argumentListNonEmpty.KEY) | .ACTIONS => some (argumentListNonEmpty.ACTIONS) | .STATE => some (argumentListNonEmpty.STATE) | .ENTRIES => some (argumentListNonEmpty.ENTRIES) | .TYPE => some (argumentListNonEmpty.TYPE) | .PRIORITY => some (argumentListNonEmpty.PRIORITY) | .«_ID '.' %» field0 => some (argumentListNonEmpty.«_ID '.' %» field0) | .THIS => some (argumentListNonEmpty.THIS) | .«'...'» => some (argumentListNonEmpty.«'...'») | .«% %» field0 field1 => some (argumentListNonEmpty.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (argumentListNonEmpty.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (argumentListNonEmpty.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (argumentListNonEmpty.«`( % `) %» field0 field1) | .«'{#}'» => some (argumentListNonEmpty.«'{#}'») | .«`{ % % `}» field0 field1 => some (argumentListNonEmpty.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (argumentListNonEmpty.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (argumentListNonEmpty.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (argumentListNonEmpty.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (argumentListNonEmpty.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (argumentListNonEmpty.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (argumentListNonEmpty.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (argumentListNonEmpty.«`( % `)» field0) | .«% '=' %» field0 field1 => some (argumentListNonEmpty.«% '=' %» field0 field1) | .«% '=' '_'» field0 => some (argumentListNonEmpty.«% '=' '_'» field0) | .«'_'» => some (argumentListNonEmpty.«'_'») | .«% ',' %» field0 field1 => some (argumentListNonEmpty.«% ',' %» field0 field1) | _ => none


inductive lvalue : Type where
  | _ID : _root_.String → lvalue
  | APPLY : lvalue
  | KEY : lvalue
  | ACTIONS : lvalue
  | STATE : lvalue
  | ENTRIES : lvalue
  | TYPE : lvalue
  | PRIORITY : lvalue
  | «_ID '.' %» : nonTypeName → lvalue
  | THIS : lvalue
  | «% '.' %» : lvalue → member → lvalue
  | «% `[ % `]» : lvalue → expression → lvalue
  | «% `[ % % % `]» : lvalue → expression → sliceop → expression → lvalue
  | «`( % `)» : lvalue → lvalue
deriving _root_.DecidableEq


def «$lvalue_as_expression:case_1:downcast:0» (arg0 : lvalue) : (_root_.Option referenceExpression) := match arg0 with | ._ID field0 => some (referenceExpression._ID field0) | .APPLY => some (referenceExpression.APPLY) | .KEY => some (referenceExpression.KEY) | .ACTIONS => some (referenceExpression.ACTIONS) | .STATE => some (referenceExpression.STATE) | .ENTRIES => some (referenceExpression.ENTRIES) | .TYPE => some (referenceExpression.TYPE) | .PRIORITY => some (referenceExpression.PRIORITY) | .«_ID '.' %» field0 => some (referenceExpression.«_ID '.' %» field0) | .THIS => some (referenceExpression.THIS) | _ => none


def «$expression_as_lvalue:case_1:downcast:0» (arg0 : expression) : (_root_.Option referenceExpression) := match arg0 with | ._ID field0 => some (referenceExpression._ID field0) | .APPLY => some (referenceExpression.APPLY) | .KEY => some (referenceExpression.KEY) | .ACTIONS => some (referenceExpression.ACTIONS) | .STATE => some (referenceExpression.STATE) | .ENTRIES => some (referenceExpression.ENTRIES) | .TYPE => some (referenceExpression.TYPE) | .PRIORITY => some (referenceExpression.PRIORITY) | .«_ID '.' %» field0 => some (referenceExpression.«_ID '.' %» field0) | .THIS => some (referenceExpression.THIS) | _ => none


def «$expression_as_lvalue:case_2:downcast:0» (arg0 : expression) : (_root_.Option memberAccessExpression) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpression.«% '.' %» field0 field1) | _ => none


def «$expression_as_lvalue:case_2:downcast:1» (arg0 : memberAccessBase) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «$expression_as_lvalue:case_3:downcast:0» (arg0 : expression) : (_root_.Option indexAccessExpression) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpression.«% `[ % `]» field0 field1) | _ => none


def «$expression_as_lvalue:case_4:downcast:0» (arg0 : expression) : (_root_.Option sliceAccessExpression) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpression.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$expression_as_lvalue:case_5:downcast:0» (arg0 : expression) : (_root_.Option sliceAccessExpression) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpression.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$expression_as_lvalue:case_6:downcast:0» (arg0 : expression) : (_root_.Option parenthesizedExpression) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpression.«`( % `)» field0) | _ => none


inductive emptyStatement : Type where
  | «';'» : emptyStatement
deriving _root_.DecidableEq


inductive assignop : Type where
  | «'='» : assignop
  | «'+='» : assignop
  | «'-='» : assignop
  | «'|+|='» : assignop
  | «'|-|='» : assignop
  | «'*='» : assignop
  | «'/='» : assignop
  | «'%='» : assignop
  | «'<<='» : assignop
  | «'>>='» : assignop
  | «'&='» : assignop
  | «'^='» : assignop
  | «'|='» : assignop
deriving _root_.DecidableEq


inductive assignmentStatement : Type where
  | «% % % ';'» : lvalue → assignop → expression → assignmentStatement
deriving _root_.DecidableEq


inductive callStatement : Type where
  | «% `( % `) ';'» : lvalue → argumentList → callStatement
  | «% `< % `> `( % `) ';'» : lvalue → typeArgumentList → argumentList → callStatement
deriving _root_.DecidableEq


inductive directApplicationStatement : Type where
  | «% '.' APPLY `( % `) ';'» : namedType → argumentList → directApplicationStatement
deriving _root_.DecidableEq


inductive returnStatement : Type where
  | «RETURN ';'» : returnStatement
  | «RETURN % ';'» : expression → returnStatement
deriving _root_.DecidableEq


inductive exitStatement : Type where
  | «EXIT ';'» : exitStatement
deriving _root_.DecidableEq


inductive forUpdateStatement : Type where
  | «% `( % `)» : lvalue → argumentList → forUpdateStatement
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forUpdateStatement
  | «% % %» : lvalue → assignop → expression → forUpdateStatement
deriving _root_.DecidableEq


inductive forUpdateStatementListNonEmpty : Type where
  | «% `( % `)» : lvalue → argumentList → forUpdateStatementListNonEmpty
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forUpdateStatementListNonEmpty
  | «% % %» : lvalue → assignop → expression → forUpdateStatementListNonEmpty
  | «% ',' %» : forUpdateStatementListNonEmpty → forUpdateStatement → forUpdateStatementListNonEmpty
deriving _root_.DecidableEq


inductive forUpdateStatementList : Type where
  | _EMPTY : forUpdateStatementList
  | «% `( % `)» : lvalue → argumentList → forUpdateStatementList
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forUpdateStatementList
  | «% % %» : lvalue → assignop → expression → forUpdateStatementList
  | «% ',' %» : forUpdateStatementListNonEmpty → forUpdateStatement → forUpdateStatementList
deriving _root_.DecidableEq


def «$flatten_forUpdateStatementList:case_2:downcast:0» (arg0 : forUpdateStatementList) : (_root_.Option forUpdateStatement) := match arg0 with | .«% `( % `)» field0 field1 => some (forUpdateStatement.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (forUpdateStatement.«% `< % `> `( % `)» field0 field1 field2) | .«% % %» field0 field1 field2 => some (forUpdateStatement.«% % %» field0 field1 field2) | _ => none


def «$flatten_forUpdateStatementList:case_3:downcast:0» (arg0 : forUpdateStatementList) : (_root_.Option forUpdateStatementListNonEmpty) := match arg0 with | .«% `( % `)» field0 field1 => some (forUpdateStatementListNonEmpty.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (forUpdateStatementListNonEmpty.«% `< % `> `( % `)» field0 field1 field2) | .«% % %» field0 field1 field2 => some (forUpdateStatementListNonEmpty.«% % %» field0 field1 field2) | .«% ',' %» field0 field1 => some (forUpdateStatementListNonEmpty.«% ',' %» field0 field1) | _ => none


inductive forCollectionExpression : Type where
  | TRUE : forCollectionExpression
  | FALSE : forCollectionExpression
  | D : _root_.Int → forCollectionExpression
  | «% W %» : _root_.Nat → _root_.Int → forCollectionExpression
  | «% S %» : _root_.Nat → _root_.Int → forCollectionExpression
  | «'"' % '"'» : _root_.String → forCollectionExpression
  | _ID : _root_.String → forCollectionExpression
  | APPLY : forCollectionExpression
  | KEY : forCollectionExpression
  | ACTIONS : forCollectionExpression
  | STATE : forCollectionExpression
  | ENTRIES : forCollectionExpression
  | TYPE : forCollectionExpression
  | PRIORITY : forCollectionExpression
  | «_ID '.' %» : nonTypeName → forCollectionExpression
  | THIS : forCollectionExpression
  | «'...'» : forCollectionExpression
  | «% %» : unop → expression → forCollectionExpression
  | «% % %» : expression → binop → expression → forCollectionExpression
  | «% '?' % ':' %» : expression → expression → expression → forCollectionExpression
  | «`( % `) %» : type → expression → forCollectionExpression
  | «'{#}'» : forCollectionExpression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → forCollectionExpression
  | «ERROR '.' %» : member → forCollectionExpression
  | «% '.' %» : memberAccessBase → member → forCollectionExpression
  | «% `[ % `]» : expression → expression → forCollectionExpression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → forCollectionExpression
  | «% `( % `)» : callTarget → argumentList → forCollectionExpression
  | «% `< % `> `( % `)» : callableTarget → realTypeArgumentList → argumentList → forCollectionExpression
  | «`( % `)» : expression → forCollectionExpression
  | «% '..' %» : expression → expression → forCollectionExpression
deriving _root_.DecidableEq

end SpecTec
