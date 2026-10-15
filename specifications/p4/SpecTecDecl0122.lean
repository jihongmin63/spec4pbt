import SpecTecDecl0121

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:dataExpressionIR:sequenceExpressionIR» : dataExpressionIR → Bool
  | .«SEQ `{ % `}» _ => true
  | .«SEQ `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:dataTypeIR:arrayTypeIR» : dataTypeIR → Bool
  | .«ARRAY % `[ % `]» _ _ => true
  | _ => false


def «sub:dataTypeIR:headerStackTypeIR» : dataTypeIR → Bool
  | .«HEADER_STACK % `[ % `]» _ _ => true
  | _ => false


def «sub:dataTypeIR:listTypeIR» : dataTypeIR → Bool
  | .«LIST `< % `>» _ => true
  | _ => false


def «sub:dataTypeIR:serializableEnumTypeIR» : dataTypeIR → Bool
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:dataTypeIR:simpleEnumTypeIR» : dataTypeIR → Bool
  | .«ENUM % `{ % `}» _ _ => true
  | _ => false


def «sub:dataTypeIR:tupleTypeIR» : dataTypeIR → Bool
  | .«TUPLE `< % `>» _ => true
  | _ => false


def «sub:declaration:actionDeclaration» : declaration → Bool
  | .«% ACTION % `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:declaration:constantDeclaration» : declaration → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:declaration:controlDeclaration» : declaration → Bool
  | .«% CONTROL % % `( % `) % `{ % APPLY % `}» _ _ _ _ _ _ _ => true
  | _ => false


def «sub:declaration:controlTypeDeclaration» : declaration → Bool
  | .«% CONTROL % % `( % `) ';'» _ _ _ _ => true
  | _ => false


def «sub:declaration:enumTypeDeclaration» : declaration → Bool
  | .«% ENUM % `{ % % `}» _ _ _ _ => true
  | .«% ENUM % % `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:declaration:errorDeclaration» : declaration → Bool
  | .«ERROR `{ % `}» _ => true
  | _ => false


def «sub:declaration:externFunctionDeclaration» : declaration → Bool
  | .«% EXTERN % ';'» _ _ => true
  | _ => false


def «sub:declaration:externObjectDeclaration» : declaration → Bool
  | .«% EXTERN % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declaration:functionDeclaration» : declaration → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:declaration:headerTypeDeclaration» : declaration → Bool
  | .«% HEADER % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declaration:headerUnionTypeDeclaration» : declaration → Bool
  | .«% HEADER_UNION % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declaration:instantiation» : declaration → Bool
  | .«% % `( % `) % ';'» _ _ _ _ => true
  | .«% % `( % `) % % ';'» _ _ _ _ _ => true
  | _ => false


def «sub:declaration:matchKindDeclaration» : declaration → Bool
  | .«MATCH_KIND `{ % % `}» _ _ => true
  | _ => false


def «sub:declaration:packageTypeDeclaration» : declaration → Bool
  | .«% PACKAGE % % `( % `) ';'» _ _ _ _ => true
  | _ => false


def «sub:declaration:parserDeclaration» : declaration → Bool
  | .«% PARSER % % `( % `) % `{ % % `}» _ _ _ _ _ _ _ => true
  | _ => false


def «sub:declaration:parserTypeDeclaration» : declaration → Bool
  | .«% PARSER % % `( % `) ';'» _ _ _ _ => true
  | _ => false


def «sub:declaration:structTypeDeclaration» : declaration → Bool
  | .«% STRUCT % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declaration:typedefDeclaration» : declaration → Bool
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | .«% TYPE % % ';'» _ _ _ => true
  | _ => false


def «sub:declarationIR:actionDeclarationIR» : declarationIR → Bool
  | .«% ACTION % `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:constantDeclarationIR» : declarationIR → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:controlDeclarationIR» : declarationIR → Bool
  | .«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» _ _ _ _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:controlTypeDeclarationIR» : declarationIR → Bool
  | .«% CONTROL % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:declarationIR:derivedTypeDeclarationIR» : declarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:enumTypeDeclarationIR» : declarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:declarationIR:errorDeclarationIR» : declarationIR → Bool
  | .«ERROR `{ % `}» _ => true
  | _ => false

end SpecTec
