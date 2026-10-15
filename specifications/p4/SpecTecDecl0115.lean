import SpecTecDecl0114

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:parserConditionalStatement:IF `( % `) % ELSE %» : parserConditionalStatement → Bool
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «exec:match:parserConditionalStatementIR:IF `( % `) %» : parserConditionalStatementIR → Bool
  | .«IF `( % `) %» _ _ => true
  | _ => false


def «exec:match:parserConditionalStatementIR:IF `( % `) % ELSE %» : parserConditionalStatementIR → Bool
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «exec:match:parserLocalDeclarationList:% %» : parserLocalDeclarationList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:parserLocalDeclarationList:_EMPTY» : parserLocalDeclarationList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:parserStateList:% %» : parserStateList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:prefixedNameIR:'.' %» : prefixedNameIR → Bool
  | .«'.' %» _ => true
  | _ => false


def «exec:match:prefixedNameIR:_BARE» : prefixedNameIR → Bool
  | ._BARE _ => true
  | _ => false


def «exec:match:prefixedNonTypeName:_ID '.' %» : prefixedNonTypeName → Bool
  | .«_ID '.' %» _ => true
  | _ => false


def «exec:match:prefixedTypeName:_TID '.' %» : prefixedTypeName → Bool
  | .«_TID '.' %» _ => true
  | _ => false


def «exec:match:realTypeArgumentList:% ',' %» : realTypeArgumentList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:recordElementExpression:% '=' %» : recordElementExpression → Bool
  | .«% '=' %» _ _ => true
  | _ => false


def «exec:match:recordElementExpression:% '=' % ',' %» : recordElementExpression → Bool
  | .«% '=' % ',' %» _ _ _ => true
  | _ => false


def «exec:match:recordElementExpression:% '=' % ',' % ',' '...'» : recordElementExpression → Bool
  | .«% '=' % ',' % ',' '...'» _ _ _ => true
  | _ => false


def «exec:match:recordElementExpression:% '=' % ',' '...'» : recordElementExpression → Bool
  | .«% '=' % ',' '...'» _ _ => true
  | _ => false


def «exec:match:recordExpressionIR:RECORD `{ % ',' '...' `}» : recordExpressionIR → Bool
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «exec:match:recordExpressionIR:RECORD `{ % `}» : recordExpressionIR → Bool
  | .«RECORD `{ % `}» _ => true
  | _ => false


def «exec:match:recordTypeIR:RECORD `{ % ',' '...' `}» : recordTypeIR → Bool
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «exec:match:recordTypeIR:RECORD `{ % `}» : recordTypeIR → Bool
  | .«RECORD `{ % `}» _ => true
  | _ => false


def «exec:match:recordValue:RECORD `{ % ',' '...' `}» : recordValue → Bool
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «exec:match:recordValue:RECORD `{ % `}» : recordValue → Bool
  | .«RECORD `{ % `}» _ => true
  | _ => false


def «exec:match:returnStatement:RETURN % ';'» : returnStatement → Bool
  | .«RETURN % ';'» _ => true
  | _ => false


def «exec:match:returnStatementIR:RETURN % ';'» : returnStatementIR → Bool
  | .«RETURN % ';'» _ => true
  | _ => false


def «exec:match:returnStatementIR:RETURN ';'» : returnStatementIR → Bool
  | .«RETURN ';'» => true
  | _ => false


def «exec:match:selectCaseList:% %» : selectCaseList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:selectCaseList:_EMPTY» : selectCaseList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:sequenceExpressionIR:SEQ `{ % ',' '...' `}» : sequenceExpressionIR → Bool
  | .«SEQ `{ % ',' '...' `}» _ => true
  | _ => false


def «exec:match:sequenceExpressionIR:SEQ `{ % `}» : sequenceExpressionIR → Bool
  | .«SEQ `{ % `}» _ => true
  | _ => false


def «exec:match:sequenceTypeIR:SEQ `< % ',' '...' `>» : sequenceTypeIR → Bool
  | .«SEQ `< % ',' '...' `>» _ => true
  | _ => false


def «exec:match:sequenceTypeIR:SEQ `< % `>» : sequenceTypeIR → Bool
  | .«SEQ `< % `>» _ => true
  | _ => false


def «exec:match:sequenceValue:SEQ `( % ',' '...' `)» : sequenceValue → Bool
  | .«SEQ `( % ',' '...' `)» _ => true
  | _ => false


def «exec:match:sequenceValue:SEQ `( % `)» : sequenceValue → Bool
  | .«SEQ `( % `)» _ => true
  | _ => false

end SpecTec
