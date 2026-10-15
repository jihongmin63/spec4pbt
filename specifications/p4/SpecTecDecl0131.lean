import SpecTecDecl0130

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:typeDefIR:headerUnionTypeDefIR» : typeDefIR → Bool
  | .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeDefIR:nameTypeIR» : typeDefIR → Bool
  | ._NAME _ => true
  | _ => false


def «sub:typeDefIR:newTypeIR» : typeDefIR → Bool
  | .TYPE _ _ => true
  | _ => false


def «sub:typeDefIR:packageObjectTypeDefIR» : typeDefIR → Bool
  | .«PACKAGE % `< % ',' % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:typeDefIR:parserObjectTypeDefIR» : typeDefIR → Bool
  | .«PARSER % `< % ',' % `> `( % `)» _ _ _ _ => true
  | _ => false


def «sub:typeDefIR:serializableEnumTypeIR» : typeDefIR → Bool
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeDefIR:simpleEnumTypeIR» : typeDefIR → Bool
  | .«ENUM % `{ % `}» _ _ => true
  | _ => false


def «sub:typeDefIR:structTypeDefIR» : typeDefIR → Bool
  | .«STRUCT % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeDefIR:tableObjectTypeIR» : typeDefIR → Bool
  | .«TABLE % `{ % `}» _ _ => true
  | _ => false


def «sub:typeDefIR:typedefTypeIR» : typeDefIR → Bool
  | .TYPEDEF _ _ => true
  | _ => false


def «sub:typeIR:aliasTypeIR» : typeIR → Bool
  | .TYPEDEF _ _ => true
  | .TYPE _ _ => true
  | _ => false


def «sub:typeIR:arrayTypeIR» : typeIR → Bool
  | .«ARRAY % `[ % `]» _ _ => true
  | _ => false


def «sub:typeIR:baseTypeIR» : typeIR → Bool
  | .VOID => true
  | .BOOL => true
  | .ERROR => true
  | .MATCH_KIND => true
  | .STRING => true
  | .INT => true
  | .«INT `< % `>» _ => true
  | .«BIT `< % `>» _ => true
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «sub:typeIR:boolTypeIR» : typeIR → Bool
  | .BOOL => true
  | _ => false


def «sub:typeIR:controlObjectTypeIR» : typeIR → Bool
  | .«CONTROL % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:typeIR:dataTypeIR» : typeIR → Bool
  | .«LIST `< % `>» _ => true
  | .«TUPLE `< % `>» _ => true
  | .«ARRAY % `[ % `]» _ _ => true
  | .«HEADER_STACK % `[ % `]» _ _ => true
  | .«STRUCT % `< % `> `{ % `}» _ _ _ => true
  | .«HEADER % `< % `> `{ % `}» _ _ _ => true
  | .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => true
  | .«ENUM % `{ % `}» _ _ => true
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:defaultTypeIR» : typeIR → Bool
  | .DEFAULT => true
  | _ => false


def «sub:typeIR:enumTypeIR» : typeIR → Bool
  | .«ENUM % `{ % `}» _ _ => true
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:errorTypeIR» : typeIR → Bool
  | .ERROR => true
  | _ => false


def «sub:typeIR:externObjectTypeIR» : typeIR → Bool
  | .«EXTERN % `< % `> %» _ _ _ => true
  | _ => false


def «sub:typeIR:fixedBitTypeIR» : typeIR → Bool
  | .«BIT `< % `>» _ => true
  | _ => false


def «sub:typeIR:fixedIntTypeIR» : typeIR → Bool
  | .«INT `< % `>» _ => true
  | _ => false


def «sub:typeIR:headerStackTypeIR» : typeIR → Bool
  | .«HEADER_STACK % `[ % `]» _ _ => true
  | _ => false


def «sub:typeIR:headerTypeIR» : typeIR → Bool
  | .«HEADER % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:headerUnionTypeIR» : typeIR → Bool
  | .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:intTypeIR» : typeIR → Bool
  | .INT => true
  | _ => false


def «sub:typeIR:integerTypeIR» : typeIR → Bool
  | .INT => true
  | .«INT `< % `>» _ => true
  | .«BIT `< % `>» _ => true
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «sub:typeIR:invalidHeaderTypeIR» : typeIR → Bool
  | .HEADER_INVALID => true
  | _ => false


def «sub:typeIR:listTypeIR» : typeIR → Bool
  | .«LIST `< % `>» _ => true
  | _ => false


def «sub:typeIR:nameTypeIR» : typeIR → Bool
  | ._NAME _ => true
  | _ => false


def «sub:typeIR:newTypeIR» : typeIR → Bool
  | .TYPE _ _ => true
  | _ => false


def «sub:typeIR:objectTypeIR» : typeIR → Bool
  | .«EXTERN % `< % `> %» _ _ _ => true
  | .«PARSER % `< % `> `( % `)» _ _ _ => true
  | .«CONTROL % `< % `> `( % `)» _ _ _ => true
  | .«PACKAGE % `< % `> `{ % `}» _ _ _ => true
  | .«TABLE % `{ % `}» _ _ => true
  | _ => false

end SpecTec
