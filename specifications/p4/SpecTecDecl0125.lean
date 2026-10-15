import SpecTecDecl0124

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:expressionListResult:abortResult» : expressionListResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:expressionListResult:rejectTransitionResult» : expressionListResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:expressionNonBrace:binaryExpressionNonBrace» : expressionNonBrace → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:expressionNonBrace:callExpressionNonBrace» : expressionNonBrace → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:expressionNonBrace:castExpression» : expressionNonBrace → Bool
  | .«`( % `) %» _ _ => true
  | _ => false


def «sub:expressionNonBrace:errorAccessExpression» : expressionNonBrace → Bool
  | .«ERROR '.' %» _ => true
  | _ => false


def «sub:expressionNonBrace:indexAccessExpressionNonBrace» : expressionNonBrace → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «sub:expressionNonBrace:literalExpression» : expressionNonBrace → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:expressionNonBrace:memberAccessExpressionNonBrace» : expressionNonBrace → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «sub:expressionNonBrace:parenthesizedExpression» : expressionNonBrace → Bool
  | .«`( % `)» _ => true
  | _ => false


def «sub:expressionNonBrace:referenceExpression» : expressionNonBrace → Bool
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


def «sub:expressionNonBrace:sliceAccessExpressionNonBrace» : expressionNonBrace → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «sub:expressionNonBrace:ternaryExpressionNonBrace» : expressionNonBrace → Bool
  | .«% '?' % ':' %» _ _ _ => true
  | _ => false


def «sub:expressionNonBrace:unaryExpression» : expressionNonBrace → Bool
  | .«% %» _ _ => true
  | _ => false


def «sub:expressionResult:abortResult» : expressionResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:expressionResult:exitResult» : expressionResult → Bool
  | .EXIT => true
  | _ => false


def «sub:expressionResult:rejectTransitionResult» : expressionResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:externConstructorOrMethodPrototype:externConstructorPrototype» : externConstructorOrMethodPrototype → Bool
  | .«% % `( % `) ';'» _ _ _ => true
  | _ => false


def «sub:externConstructorOrMethodPrototype:externMethodPrototype» : externConstructorOrMethodPrototype → Bool
  | .«% % ';'» _ _ => true
  | .«% ABSTRACT % ';'» _ _ => true
  | _ => false


def «sub:externDeclarationIR:externFunctionDeclarationIR» : externDeclarationIR → Bool
  | .«% EXTERN % ';'» _ _ => true
  | _ => false


def «sub:externDeclarationIR:externObjectDeclarationIR» : externDeclarationIR → Bool
  | .«% EXTERN % `< % ',' `> `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:fcf960b04819be6c86c2b39267d87cb8» : selectCaseMatchResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:forCollectionExpression:expression» : forCollectionExpression → Bool
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


def «sub:forCollectionExpressionIR:typedExpressionIR» : forCollectionExpressionIR → Bool
  | .«% '#' %» _ _ => true
  | _ => false


def «sub:forInitStatement:forUpdateStatement» : forInitStatement → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:forInitStatementIR:forUpdateStatementIR» : forInitStatementIR → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:forInitStatementList:forInitStatement» : forInitStatementList → Bool
  | .«% % % %» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:forInitStatementList:forInitStatementListNonEmpty» : forInitStatementList → Bool
  | .«% % % %» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | .«% ',' %» _ _ => true
  | _ => false


def «sub:forUpdateStatementList:forUpdateStatement» : forUpdateStatementList → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:forUpdateStatementList:forUpdateStatementListNonEmpty» : forUpdateStatementList → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«% % %» _ _ _ => true
  | .«% ',' %» _ _ => true
  | _ => false


def «sub:functionDef:definedFunctionDef» : functionDef → Bool
  | .«FUNCTION % `< % `> `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:functionDef:externFunctionDef» : functionDef → Bool
  | .«EXTERN_FUNCTION % `< % `> `( % `)» _ _ _ => true
  | _ => false

end SpecTec
