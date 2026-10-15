import SpecTecDecl0113

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:forUpdateStatementList:_EMPTY» : forUpdateStatementList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:forUpdateStatementListNonEmpty:% ',' %» : forUpdateStatementListNonEmpty → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:infer:KNOWN AS %» : infer → Bool
  | .«KNOWN AS %» _ => true
  | _ => false


def «exec:match:initializerOpt:_EMPTY» : initializerOpt → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:instantiation:% % `( % `) % % ';'» : instantiation → Bool
  | .«% % `( % `) % % ';'» _ _ _ _ _ => true
  | _ => false


def «exec:match:instantiation:% % `( % `) % ';'» : instantiation → Bool
  | .«% % `( % `) % ';'» _ _ _ _ => true
  | _ => false


def «exec:match:integerLiteral:% S %» : integerLiteral → Bool
  | .«% S %» _ _ => true
  | _ => false


def «exec:match:integerLiteral:% W %» : integerLiteral → Bool
  | .«% W %» _ _ => true
  | _ => false


def «exec:match:integerLiteral:D» : integerLiteral → Bool
  | .D _ => true
  | _ => false


def «exec:match:integerValue:% '.' % V %» : integerValue → Bool
  | .«% '.' % V %» _ _ _ => true
  | _ => false


def «exec:match:lvalue:% '.' %» : lvalue → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «exec:match:lvalue:% `[ % % % `]» : lvalue → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «exec:match:lvalue:% `[ % `]» : lvalue → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «exec:match:lvalue:`( % `)» : lvalue → Bool
  | .«`( % `)» _ => true
  | _ => false


def «exec:match:lvalueIR:% '.' %» : lvalueIR → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «exec:match:lvalueIR:% `[ % % % `]» : lvalueIR → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «exec:match:lvalueIR:% `[ % `]» : lvalueIR → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «exec:match:lvalueIR:`( % `)» : lvalueIR → Bool
  | .«`( % `)» _ => true
  | _ => false


def «exec:match:matchMode:LPM» : matchMode → Bool
  | .LPM _ => true
  | _ => false


def «exec:match:memberAccessBaseIR:TYPE» : memberAccessBaseIR → Bool
  | .TYPE _ => true
  | _ => false


def «exec:match:nameList:% ',' %» : nameList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:namedExpressionList:% ',' %» : namedExpressionList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:nonEmptyParameterList:% ',' %» : nonEmptyParameterList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:objectDeclarationList:% %» : objectDeclarationList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:objectDeclarationList:_EMPTY» : objectDeclarationList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:p4program:% %» : p4program → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:p4program:% ';'» : p4program → Bool
  | .«% ';'» _ => true
  | _ => false


def «exec:match:p4program:_EMPTY» : p4program → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:parameterList:_EMPTY» : parameterList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:parserBlockElementStatementList:% %» : parserBlockElementStatementList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:parserBlockElementStatementList:_EMPTY» : parserBlockElementStatementList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:parserConditionalStatement:IF `( % `) %» : parserConditionalStatement → Bool
  | .«IF `( % `) %» _ _ => true
  | _ => false

end SpecTec
