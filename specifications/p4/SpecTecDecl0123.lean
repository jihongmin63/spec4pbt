import SpecTecDecl0122

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:declarationIR:externDeclarationIR» : declarationIR → Bool
  | .«% EXTERN % ';'» _ _ => true
  | .«% EXTERN % `< % ',' `> `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:externFunctionDeclarationIR» : declarationIR → Bool
  | .«% EXTERN % ';'» _ _ => true
  | _ => false


def «sub:declarationIR:externObjectDeclarationIR» : declarationIR → Bool
  | .«% EXTERN % `< % ',' `> `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:functionDeclarationIR» : declarationIR → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:declarationIR:headerTypeDeclarationIR» : declarationIR → Bool
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:headerUnionTypeDeclarationIR» : declarationIR → Bool
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:instantiationIR» : declarationIR → Bool
  | .«% % % `( % `) % % ';'» _ _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:matchKindDeclarationIR» : declarationIR → Bool
  | .«MATCH_KIND `{ % `}» _ => true
  | _ => false


def «sub:declarationIR:packageTypeDeclarationIR» : declarationIR → Bool
  | .«% PACKAGE % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:parserDeclarationIR» : declarationIR → Bool
  | .«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» _ _ _ _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:parserTypeDeclarationIR» : declarationIR → Bool
  | .«% PARSER % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:structTypeDeclarationIR» : declarationIR → Bool
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:typeDeclarationIR» : declarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | .«% TYPE % % ';'» _ _ _ => true
  | .«% PARSER % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | .«% CONTROL % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | .«% PACKAGE % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:typedefDeclarationIR» : declarationIR → Bool
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | .«% TYPE % % ';'» _ _ _ => true
  | _ => false


def «sub:declarationResult:continueEmptyResult» : declarationResult → Bool
  | ._EMPTY => true
  | _ => false


def «sub:declarationResult:exitResult» : declarationResult → Bool
  | .EXIT => true
  | _ => false


def «sub:declarationResult:rejectTransitionResult» : declarationResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:derivedTypeDeclarationIR:enumTypeDeclarationIR» : derivedTypeDeclarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:derivedTypeDeclarationIR:headerTypeDeclarationIR» : derivedTypeDeclarationIR → Bool
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:derivedTypeDeclarationIR:headerUnionTypeDeclarationIR» : derivedTypeDeclarationIR → Bool
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:derivedTypeDeclarationIR:structTypeDeclarationIR» : derivedTypeDeclarationIR → Bool
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:e6b280c1e226de067f00ca0ea4d2396a» : calleeResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:enumTypeIR:serializableEnumTypeIR» : enumTypeIR → Bool
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:expression:binaryExpression» : expression → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:expression:booleanLiteral» : expression → Bool
  | .TRUE => true
  | .FALSE => true
  | _ => false


def «sub:expression:callExpression» : expression → Bool
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:expression:castExpression» : expression → Bool
  | .«`( % `) %» _ _ => true
  | _ => false


def «sub:expression:defaultExpression» : expression → Bool
  | .«'...'» => true
  | _ => false


def «sub:expression:errorAccessExpression» : expression → Bool
  | .«ERROR '.' %» _ => true
  | _ => false


def «sub:expression:indexAccessExpression» : expression → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «sub:expression:integerLiteral» : expression → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | _ => false


def «sub:expression:invalidHeaderExpression» : expression → Bool
  | .«'{#}'» => true
  | _ => false

end SpecTec
