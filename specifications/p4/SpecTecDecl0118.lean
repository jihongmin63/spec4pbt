import SpecTecDecl0117

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:typeParameterListOpt:_EMPTY» : typeParameterListOpt → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:typeParameterListOpt:`< % `>» : typeParameterListOpt → Bool
  | .«`< % `>» _ => true
  | _ => false


def «exec:match:typedefDeclaration:% TYPE % % ';'» : typedefDeclaration → Bool
  | .«% TYPE % % ';'» _ _ _ => true
  | _ => false


def «exec:match:typedefDeclaration:% TYPEDEF % % ';'» : typedefDeclaration → Bool
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | _ => false


def «exec:match:typedefDeclarationIR:% TYPE % % ';'» : typedefDeclarationIR → Bool
  | .«% TYPE % % ';'» _ _ _ => true
  | _ => false


def «exec:match:typedefDeclarationIR:% TYPEDEF % % ';'» : typedefDeclarationIR → Bool
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | _ => false


def «exec:match:unop:'!'» : unop → Bool
  | .«'!'» => true
  | _ => false


def «exec:match:unop:'+'» : unop → Bool
  | .«'+'» => true
  | _ => false


def «exec:match:unop:'-'» : unop → Bool
  | .«'-'» => true
  | _ => false


def «exec:match:unop:'~'» : unop → Bool
  | .«'~'» => true
  | _ => false


def «sub:00ef2590c406b2e80674abdc88a5f791» : simpleKeysetExpressionResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:2696123d73629c1405602c6f46e71ef0» : tableMatchResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:55405fd0e89a4eb8be34279082551b13» : keysetExpressionResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:5bbdc400ae580196ad190cb78bdb96be» : expressionResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:892bb582f6d65aa393b18ac5ebd27efe» : copyInArgumentResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:9224fbf21f8bc3a297aa7bfded73bbed» : storageReferenceResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:a7724a2c6fd1c0768de65582fd30ad49» : copyInResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:a93d2d0204d29057f4469a3ea2887552» : tableKeysResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:accessExpressionIR:errorAccessExpressionIR» : accessExpressionIR → Bool
  | .«ERROR '.' %» _ => true
  | _ => false


def «sub:accessExpressionIR:indexAccessExpressionIR» : accessExpressionIR → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «sub:accessExpressionIR:memberAccessExpressionIR» : accessExpressionIR → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «sub:accessExpressionIR:sliceAccessExpressionIR» : accessExpressionIR → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «sub:actionResult:exitResult» : actionResult → Bool
  | .EXIT => true
  | _ => false


def «sub:aliasTypeIR:newTypeIR» : aliasTypeIR → Bool
  | .TYPE _ _ => true
  | _ => false


def «sub:aliasTypeIR:typedefTypeIR» : aliasTypeIR → Bool
  | .TYPEDEF _ _ => true
  | _ => false


def «sub:annotationList:annotation» : annotationList → Bool
  | .«'@' %» _ => true
  | .«'@' % `( % `)» _ _ => true
  | .«'@' % `[ % `]» _ _ => true
  | .«'@' PRAGMA % %» _ _ => true
  | _ => false


def «sub:annotationList:annotationListNonEmpty» : annotationList → Bool
  | .«'@' %» _ => true
  | .«'@' % `( % `)» _ _ => true
  | .«'@' % `[ % `]» _ _ => true
  | .«'@' PRAGMA % %» _ _ => true
  | .«% %» _ _ => true
  | _ => false


def «sub:annotationToken:integerLiteral» : annotationToken → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | _ => false


def «sub:argument:expression» : argument → Bool
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


def «sub:argumentIR:typedExpressionIR» : argumentIR → Bool
  | .«% '#' %» _ _ => true
  | _ => false


def «sub:argumentList:argument» : argumentList → Bool
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
  | .«% '=' %» _ _ => true
  | .«% '=' '_'» _ => true
  | .«'_'» => true
  | _ => false


def «sub:argumentList:argumentListNonEmpty» : argumentList → Bool
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
  | .«% '=' %» _ _ => true
  | .«% '=' '_'» _ => true
  | .«'_'» => true
  | .«% ',' %» _ _ => true
  | _ => false

end SpecTec
