import SpecTecDecl0128

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:statement:callStatement» : statement → Bool
  | .«% `( % `) ';'» _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | _ => false


def «sub:statement:conditionalStatement» : statement → Bool
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:statement:continueStatement» : statement → Bool
  | .«CONTINUE ';'» => true
  | _ => false


def «sub:statement:directApplicationStatement» : statement → Bool
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | _ => false


def «sub:statement:emptyStatement» : statement → Bool
  | .«';'» => true
  | _ => false


def «sub:statement:exitStatement» : statement → Bool
  | .«EXIT ';'» => true
  | _ => false


def «sub:statement:forStatement» : statement → Bool
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | _ => false


def «sub:statement:returnStatement» : statement → Bool
  | .«RETURN ';'» => true
  | .«RETURN % ';'» _ => true
  | _ => false


def «sub:statement:switchStatement» : statement → Bool
  | .«SWITCH `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:statementIR:assignmentStatementIR» : statementIR → Bool
  | .«% % % ';'» _ _ _ => true
  | _ => false


def «sub:statementIR:blockStatementIR» : statementIR → Bool
  | .«% `{ % `}» _ _ => true
  | _ => false


def «sub:statementIR:breakStatement» : statementIR → Bool
  | .«BREAK ';'» => true
  | _ => false


def «sub:statementIR:callStatementIR» : statementIR → Bool
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | _ => false


def «sub:statementIR:conditionalStatementIR» : statementIR → Bool
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:statementIR:continueStatement» : statementIR → Bool
  | .«CONTINUE ';'» => true
  | _ => false


def «sub:statementIR:directApplicationStatementIR» : statementIR → Bool
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | _ => false


def «sub:statementIR:emptyStatement» : statementIR → Bool
  | .«';'» => true
  | _ => false


def «sub:statementIR:exitStatement» : statementIR → Bool
  | .«EXIT ';'» => true
  | _ => false


def «sub:statementIR:forStatementIR» : statementIR → Bool
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | _ => false


def «sub:statementIR:returnStatementIR» : statementIR → Bool
  | .«RETURN ';'» => true
  | .«RETURN % ';'» _ => true
  | _ => false


def «sub:statementIR:switchStatementIR» : statementIR → Bool
  | .«SWITCH `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:statementResult:abortResult» : statementResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:statementResult:continueEmptyResult» : statementResult → Bool
  | ._EMPTY => true
  | _ => false


def «sub:statementResult:exitResult» : statementResult → Bool
  | .EXIT => true
  | _ => false


def «sub:statementResult:forBreakResult» : statementResult → Bool
  | .BREAK => true
  | _ => false


def «sub:statementResult:rejectTransitionResult» : statementResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:statementResult:returnResult» : statementResult → Bool
  | .RETURN _ => true
  | _ => false


def «sub:storageReference:prefixedNameIR» : storageReference → Bool
  | ._BARE _ => true
  | .«'.' %» _ => true
  | _ => false


def «sub:storageReferenceResult:abortResult» : storageReferenceResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:switchLabel:expressionNonBrace» : switchLabel → Bool
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
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | _ => false


def «sub:switchLabel:prefixedNonTypeName» : switchLabel → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | _ => false


def «sub:switchLabelIR:typedExpressionIR» : switchLabelIR → Bool
  | .«% '#' %» _ _ => true
  | _ => false

end SpecTec
