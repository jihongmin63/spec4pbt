import SpecTecDecl0131

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:typeIR:packageObjectTypeIR» : typeIR → Bool
  | .«PACKAGE % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:parserObjectTypeIR» : typeIR → Bool
  | .«PARSER % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:typeIR:recordTypeIR» : typeIR → Bool
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:typeIR:sequenceTypeIR» : typeIR → Bool
  | .«SEQ `< % `>» _ => true
  | .«SEQ `< % ',' '...' `>» _ => true
  | _ => false


def «sub:typeIR:serializableEnumTypeIR» : typeIR → Bool
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:setTypeIR» : typeIR → Bool
  | .«SET `< % `>» _ => true
  | _ => false


def «sub:typeIR:simpleEnumTypeIR» : typeIR → Bool
  | .«ENUM % `{ % `}» _ _ => true
  | _ => false


def «sub:typeIR:stringTypeIR» : typeIR → Bool
  | .STRING => true
  | _ => false


def «sub:typeIR:structTypeIR» : typeIR → Bool
  | .«STRUCT % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeIR:synthesizedTypeIR» : typeIR → Bool
  | .DEFAULT => true
  | .HEADER_INVALID => true
  | .«SEQ `< % `>» _ => true
  | .«SEQ `< % ',' '...' `>» _ => true
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | .«SET `< % `>» _ => true
  | .«TABLE_ENUM % `{ % `}» _ _ => true
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => true
  | _ => false


def «sub:typeIR:tableMetadataEnumTypeIR» : typeIR → Bool
  | .«TABLE_ENUM % `{ % `}» _ _ => true
  | _ => false


def «sub:typeIR:tableMetadataStructTypeIR» : typeIR → Bool
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => true
  | _ => false


def «sub:typeIR:tableMetadataTypeIR» : typeIR → Bool
  | .«TABLE_ENUM % `{ % `}» _ _ => true
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => true
  | _ => false


def «sub:typeIR:tableObjectTypeIR» : typeIR → Bool
  | .«TABLE % `{ % `}» _ _ => true
  | _ => false


def «sub:typeIR:tupleTypeIR» : typeIR → Bool
  | .«TUPLE `< % `>» _ => true
  | _ => false


def «sub:typeIR:typedefTypeIR» : typeIR → Bool
  | .TYPEDEF _ _ => true
  | _ => false


def «sub:typeIR:varBitTypeIR» : typeIR → Bool
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «sub:typeIR:voidTypeIR» : typeIR → Bool
  | .VOID => true
  | _ => false


def «sub:typeOrVoid:arrayType» : typeOrVoid → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «sub:typeOrVoid:baseType» : typeOrVoid → Bool
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
  | _ => false


def «sub:typeOrVoid:identifier» : typeOrVoid → Bool
  | ._ID _ => true
  | _ => false


def «sub:typeOrVoid:listType» : typeOrVoid → Bool
  | .«LIST `< % `>» _ => true
  | _ => false


def «sub:typeOrVoid:prefixedTypeName» : typeOrVoid → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | _ => false


def «sub:typeOrVoid:specializedType» : typeOrVoid → Bool
  | .«% `< % `>» _ _ => true
  | _ => false


def «sub:typeOrVoid:tupleType» : typeOrVoid → Bool
  | .«TUPLE `< % `>» _ => true
  | _ => false


def «sub:typeParameterList:name» : typeParameterList → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | ._TID _ => true
  | .LIST => true
  | _ => false


def «sub:typedef:derivedTypeDeclaration» : typedef → Bool
  | .«% ENUM % `{ % % `}» _ _ _ _ => true
  | .«% ENUM % % `{ % % `}» _ _ _ _ _ => true
  | .«% STRUCT % % `{ % `}» _ _ _ _ => true
  | .«% HEADER % % `{ % `}» _ _ _ _ => true
  | .«% HEADER_UNION % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:typedef:type» : typedef → Bool
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
  | _ => false


def «sub:typedefIR:derivedTypeDeclarationIR» : typedefIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:typedefIR:typeIR» : typedefIR → Bool
  | .VOID => true
  | .BOOL => true
  | .ERROR => true
  | .MATCH_KIND => true
  | .STRING => true
  | .INT => true
  | .«INT `< % `>» _ => true
  | .«BIT `< % `>» _ => true
  | .«VARBIT `< % `>» _ => true
  | ._NAME _ => true
  | .TYPEDEF _ _ => true
  | .TYPE _ _ => true
  | .«LIST `< % `>» _ => true
  | .«TUPLE `< % `>» _ => true
  | .«ARRAY % `[ % `]» _ _ => true
  | .«HEADER_STACK % `[ % `]» _ _ => true
  | .«STRUCT % `< % `> `{ % `}» _ _ _ => true
  | .«HEADER % `< % `> `{ % `}» _ _ _ => true
  | .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => true
  | .«ENUM % `{ % `}» _ _ => true
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | .«EXTERN % `< % `> %» _ _ _ => true
  | .«PARSER % `< % `> `( % `)» _ _ _ => true
  | .«CONTROL % `< % `> `( % `)» _ _ _ => true
  | .«PACKAGE % `< % `> `{ % `}» _ _ _ => true
  | .«TABLE % `{ % `}» _ _ => true
  | .DEFAULT => true
  | .HEADER_INVALID => true
  | .«SEQ `< % `>» _ => true
  | .«SEQ `< % ',' '...' `>» _ => true
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | .«SET `< % `>» _ => true
  | .«TABLE_ENUM % `{ % `}» _ _ => true
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => true
  | _ => false


def «sub:value:arrayValue» : value → Bool
  | .«ARRAY `[ % `]» _ => true
  | _ => false


def «sub:value:boolValue» : value → Bool
  | ._B _ => true
  | _ => false

end SpecTec
