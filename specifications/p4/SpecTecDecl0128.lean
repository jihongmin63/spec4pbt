import SpecTecDecl0127

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:parserLocalDeclarationIR:variableDeclarationIR» : parserLocalDeclarationIR → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserStateList:parserState» : parserStateList → Bool
  | .«% STATE % `{ % % `}» _ _ _ _ => true
  | _ => false


def «sub:parserStatement:assignmentStatement» : parserStatement → Bool
  | .«% % % ';'» _ _ _ => true
  | _ => false


def «sub:parserStatement:callStatement» : parserStatement → Bool
  | .«% `( % `) ';'» _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | _ => false


def «sub:parserStatement:directApplicationStatement» : parserStatement → Bool
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | _ => false


def «sub:parserStatement:emptyStatement» : parserStatement → Bool
  | .«';'» => true
  | _ => false


def «sub:parserStatement:parserBlockStatement» : parserStatement → Bool
  | .«% `{ % `}» _ _ => true
  | _ => false


def «sub:parserStatement:parserConditionalStatement» : parserStatement → Bool
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:parserStatementIR:assignmentStatementIR» : parserStatementIR → Bool
  | .«% % % ';'» _ _ _ => true
  | _ => false


def «sub:parserStatementIR:callStatementIR» : parserStatementIR → Bool
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | _ => false


def «sub:parserStatementIR:directApplicationStatementIR» : parserStatementIR → Bool
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | _ => false


def «sub:parserStatementIR:emptyStatement» : parserStatementIR → Bool
  | .«';'» => true
  | _ => false


def «sub:parserStatementIR:parserBlockStatementIR» : parserStatementIR → Bool
  | .«% `{ % `}» _ _ => true
  | _ => false


def «sub:parserStatementIR:parserConditionalStatementIR» : parserStatementIR → Bool
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:parserStatementResult:continueEmptyResult» : parserStatementResult → Bool
  | ._EMPTY => true
  | _ => false


def «sub:parserStatementResult:rejectTransitionResult» : parserStatementResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:prefixedNonTypeName:nonTypeName» : prefixedNonTypeName → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | _ => false


def «sub:prefixedTypeName:typeIdentifier» : prefixedTypeName → Bool
  | ._TID _ => true
  | _ => false


def «sub:realTypeArgumentList:realTypeArgument» : realTypeArgumentList → Bool
  | .BOOL => true
  | .ERROR => true
  | .MATCH_KIND => true
  | .STRING => true
  | .INT => true
  | .«INT `< % `>» _ => true
  | .«INT `< `( % `) `>» _ => true
  | .BIT => true
  | .«BIT `< % `>» _ => true
  | .«BIT `< `( % `) `>» _ => true
  | .«VARBIT `< % `>» _ => true
  | .«VARBIT `< `( % `) `>» _ => true
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | .«% `< % `>» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«LIST `< % `>» _ => true
  | .«TUPLE `< % `>» _ => true
  | .VOID => true
  | .«'_'» => true
  | _ => false


def «sub:selectCaseMatchResult:rejectTransitionResult» : selectCaseMatchResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:sequenceOrRecordElementExpression:expression» : sequenceOrRecordElementExpression → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«'...'» => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«'{#}'» => true
  | .«`{ % % `}» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | _ => false


def «sub:sequenceOrRecordElementExpression:expressionList» : sequenceOrRecordElementExpression → Bool
  | ._EMPTY => true
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«'...'» => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«'{#}'» => true
  | .«`{ % % `}» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | .«% ',' %» _ _ => true
  | _ => false


def «sub:sequenceOrRecordElementExpression:recordElementExpression» : sequenceOrRecordElementExpression → Bool
  | .«% '=' %» _ _ => true
  | .«% '=' % ',' '...'» _ _ => true
  | .«% '=' % ',' %» _ _ _ => true
  | .«% '=' % ',' % ',' '...'» _ _ _ => true
  | _ => false


def «sub:simpleKeysetExpression:expression» : simpleKeysetExpression → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«'...'» => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«'{#}'» => true
  | .«`{ % % `}» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | _ => false


def «sub:simpleKeysetExpressionIR:typedExpressionIR» : simpleKeysetExpressionIR → Bool
  | .«% '#' %» _ _ => true
  | _ => false


def «sub:simpleKeysetExpressionList:simpleKeysetExpression» : simpleKeysetExpressionList → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«'...'» => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«'{#}'» => true
  | .«`{ % % `}» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | .«% '&&&' %» _ _ => true
  | .«% '..' %» _ _ => true
  | .DEFAULT => true
  | .«'_'» => true
  | _ => false


def «sub:simpleKeysetExpressionResult:abortResult» : simpleKeysetExpressionResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:stateExpression:selectExpression» : stateExpression → Bool
  | .«SELECT `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:stateExpressionIR:selectExpressionIR» : stateExpressionIR → Bool
  | .«SELECT `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:statement:assignmentStatement» : statement → Bool
  | .«% % % ';'» _ _ _ => true
  | _ => false


def «sub:statement:blockStatement» : statement → Bool
  | .«% `{ % `}» _ _ => true
  | _ => false


def «sub:statement:breakStatement» : statement → Bool
  | .«BREAK ';'» => true
  | _ => false

end SpecTec
