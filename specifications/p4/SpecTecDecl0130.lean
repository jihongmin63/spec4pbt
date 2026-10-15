import SpecTecDecl0129

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:tableActionReference:prefixedNonTypeName» : tableActionReference → Bool
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


def «sub:tableKeyResult:exitResult» : tableKeyResult → Bool
  | .EXIT => true
  | _ => false


def «sub:tableKeysResult:exitResult» : tableKeysResult → Bool
  | .EXIT => true
  | _ => false


def «sub:tableMatchResult:exitResult» : tableMatchResult → Bool
  | .EXIT => true
  | _ => false


def «sub:tableMatchesResult:exitResult» : tableMatchesResult → Bool
  | .EXIT => true
  | _ => false


def «sub:tablePropertyIR:tableActionsPropertyIR» : tablePropertyIR → Bool
  | .«ACTIONS '=' `{ % `}» _ => true
  | _ => false


def «sub:tablePropertyIR:tableCustomPropertyIR» : tablePropertyIR → Bool
  | .«% % CUSTOM % % ';'» _ _ _ _ => true
  | .«% % CUSTOM_CONST % % ';'» _ _ _ _ => true
  | _ => false


def «sub:tablePropertyIR:tableDefaultActionPropertyIR» : tablePropertyIR → Bool
  | .«% % DEFAULT_ACTION '=' % ';'» _ _ _ => true
  | _ => false


def «sub:tablePropertyIR:tableEntriesPropertyIR» : tablePropertyIR → Bool
  | .«% % ENTRIES '=' `{ % `}» _ _ _ => true
  | _ => false


def «sub:tablePropertyIR:tableKeysPropertyIR» : tablePropertyIR → Bool
  | .«KEY '=' `{ % `}» _ => true
  | _ => false


def «sub:tableResult:exitResult» : tableResult → Bool
  | .EXIT => true
  | _ => false


def «sub:tableResult:returnResult» : tableResult → Bool
  | .RETURN _ => true
  | _ => false


def «sub:transitionResult:acceptTransitionResult» : transitionResult → Bool
  | .ACCEPT => true
  | _ => false


def «sub:transitionResult:rejectTransitionResult» : transitionResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:transitionResult:stateTransitionResult» : transitionResult → Bool
  | .STATE _ => true
  | _ => false


def «sub:type:baseType» : type → Bool
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


def «sub:type:prefixedTypeName» : type → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | _ => false


def «sub:type:specializedType» : type → Bool
  | .«% `< % `>» _ _ => true
  | _ => false


def «sub:type:tupleType» : type → Bool
  | .«TUPLE `< % `>» _ => true
  | _ => false


def «sub:typeArgument:nonTypeName» : typeArgument → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | _ => false


def «sub:typeArgument:type» : typeArgument → Bool
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


def «sub:typeArgumentList:typeArgument» : typeArgumentList → Bool
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
  | .VOID => true
  | .«'_'» => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | _ => false


def «sub:typeDeclarationIR:controlTypeDeclarationIR» : typeDeclarationIR → Bool
  | .«% CONTROL % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:typeDeclarationIR:derivedTypeDeclarationIR» : typeDeclarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | .«% STRUCT % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER % `< % `> `{ % `}» _ _ _ _ => true
  | .«% HEADER_UNION % `< % `> `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:typeDeclarationIR:packageTypeDeclarationIR» : typeDeclarationIR → Bool
  | .«% PACKAGE % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:typeDeclarationIR:parserTypeDeclarationIR» : typeDeclarationIR → Bool
  | .«% PARSER % `< % ',' % `> `( % `) ';'» _ _ _ _ _ => true
  | _ => false


def «sub:typeDeclarationIR:typedefDeclarationIR» : typeDeclarationIR → Bool
  | .«% TYPEDEF % % ';'» _ _ _ => true
  | .«% TYPE % % ';'» _ _ _ => true
  | _ => false


def «sub:typeDefIR:aliasTypeIR» : typeDefIR → Bool
  | .TYPEDEF _ _ => true
  | .TYPE _ _ => true
  | _ => false


def «sub:typeDefIR:controlObjectTypeDefIR» : typeDefIR → Bool
  | .«CONTROL % `< % ',' % `> `( % `)» _ _ _ _ => true
  | _ => false


def «sub:typeDefIR:enumTypeIR» : typeDefIR → Bool
  | .«ENUM % `{ % `}» _ _ => true
  | .«ENUM % `< % `> `{ % `}» _ _ _ => true
  | _ => false


def «sub:typeDefIR:externObjectTypeDefIR» : typeDefIR → Bool
  | .«EXTERN % `< % ',' % `> %» _ _ _ _ => true
  | _ => false


def «sub:typeDefIR:headerTypeDefIR» : typeDefIR → Bool
  | .«HEADER % `< % `> `{ % `}» _ _ _ => true
  | _ => false

end SpecTec
