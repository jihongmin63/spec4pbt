import SpecTecDecl0123

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:expression:literalExpression» : expression → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:expression:memberAccessExpression» : expression → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «sub:expression:parenthesizedExpression» : expression → Bool
  | .«`( % `)» _ => true
  | _ => false


def «sub:expression:prefixedNonTypeName» : expression → Bool
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


def «sub:expression:referenceExpression» : expression → Bool
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
  | _ => false


def «sub:expression:sequenceOrRecordExpression» : expression → Bool
  | .«`{ % % `}» _ _ => true
  | _ => false


def «sub:expression:sliceAccessExpression» : expression → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «sub:expression:stringLiteral» : expression → Bool
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:expression:ternaryExpression» : expression → Bool
  | .«% '?' % ':' %» _ _ _ => true
  | _ => false


def «sub:expression:unaryExpression» : expression → Bool
  | .«% %» _ _ => true
  | _ => false


def «sub:expressionIR:accessExpressionIR» : expressionIR → Bool
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «sub:expressionIR:binaryExpressionIR» : expressionIR → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:expressionIR:booleanLiteral» : expressionIR → Bool
  | .TRUE => true
  | .FALSE => true
  | _ => false


def «sub:expressionIR:callExpressionIR» : expressionIR → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:expressionIR:castExpressionIR» : expressionIR → Bool
  | .«`( % `) %» _ _ => true
  | _ => false


def «sub:expressionIR:dataExpressionIR» : expressionIR → Bool
  | .«'{#}'» => true
  | .«SEQ `{ % `}» _ => true
  | .«SEQ `{ % ',' '...' `}» _ => true
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:expressionIR:defaultExpression» : expressionIR → Bool
  | .«'...'» => true
  | _ => false


def «sub:expressionIR:errorAccessExpressionIR» : expressionIR → Bool
  | .«ERROR '.' %» _ => true
  | _ => false


def «sub:expressionIR:indexAccessExpressionIR» : expressionIR → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «sub:expressionIR:integerLiteral» : expressionIR → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | _ => false


def «sub:expressionIR:invalidHeaderExpression» : expressionIR → Bool
  | .«'{#}'» => true
  | _ => false


def «sub:expressionIR:literalExpression» : expressionIR → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:expressionIR:memberAccessExpressionIR» : expressionIR → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «sub:expressionIR:parenthesizedExpressionIR» : expressionIR → Bool
  | .«`( % `)» _ => true
  | _ => false


def «sub:expressionIR:prefixedNameIR» : expressionIR → Bool
  | ._BARE _ => true
  | .«'.' %» _ => true
  | _ => false


def «sub:expressionIR:recordExpressionIR» : expressionIR → Bool
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:expressionIR:sequenceExpressionIR» : expressionIR → Bool
  | .«SEQ `{ % `}» _ => true
  | .«SEQ `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:expressionIR:sliceAccessExpressionIR» : expressionIR → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «sub:expressionIR:stringLiteral» : expressionIR → Bool
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:expressionIR:ternaryExpressionIR» : expressionIR → Bool
  | .«% '?' % ':' %» _ _ _ => true
  | _ => false


def «sub:expressionIR:unaryExpressionIR» : expressionIR → Bool
  | .«% %» _ _ => true
  | _ => false


def «sub:expressionList:expression» : expressionList → Bool
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

end SpecTec
