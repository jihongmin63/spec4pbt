import SpecTecDecl0108

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:type:typeOrVoid» : type → typeOrVoid
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«INT `< `( % `) `>» a0 => (.«INT `< `( % `) `>» a0)
  | .BIT  => (.BIT )
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«BIT `< `( % `) `>» a0 => (.«BIT `< `( % `) `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)
  | .«VARBIT `< `( % `) `>» a0 => (.«VARBIT `< `( % `) `>» a0)
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«LIST `< % `>» a0 => (.«LIST `< % `>» a0)
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)


def «cast:type:typedef» : type → typedef
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«INT `< `( % `) `>» a0 => (.«INT `< `( % `) `>» a0)
  | .BIT  => (.BIT )
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«BIT `< `( % `) `>» a0 => (.«BIT `< `( % `) `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)
  | .«VARBIT `< `( % `) `>» a0 => (.«VARBIT `< `( % `) `>» a0)
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«LIST `< % `>» a0 => (.«LIST `< % `>» a0)
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)


def «cast:typeArgument:typeArgumentList» : typeArgument → typeArgumentList
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«INT `< `( % `) `>» a0 => (.«INT `< `( % `) `>» a0)
  | .BIT  => (.BIT )
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«BIT `< `( % `) `>» a0 => (.«BIT `< `( % `) `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)
  | .«VARBIT `< `( % `) `>» a0 => (.«VARBIT `< `( % `) `>» a0)
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«LIST `< % `>» a0 => (.«LIST `< % `>» a0)
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)
  | .VOID  => (.VOID )
  | .«'_'»  => (.«'_'» )
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:typeDeclaration:declaration» : typeDeclaration → declaration
  | .«% ENUM % `{ % % `}» a0 a1 a2 a3 => (.«% ENUM % `{ % % `}» a0 a1 a2 a3)
  | .«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4 => (.«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4)
  | .«% STRUCT % % `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3)
  | .«% TYPEDEF % % ';'» a0 a1 a2 => (.«% TYPEDEF % % ';'» a0 a1 a2)
  | .«% TYPE % % ';'» a0 a1 a2 => (.«% TYPE % % ';'» a0 a1 a2)
  | .«% PARSER % % `( % `) ';'» a0 a1 a2 a3 => (.«% PARSER % % `( % `) ';'» a0 a1 a2 a3)
  | .«% CONTROL % % `( % `) ';'» a0 a1 a2 a3 => (.«% CONTROL % % `( % `) ';'» a0 a1 a2 a3)
  | .«% PACKAGE % % `( % `) ';'» a0 a1 a2 a3 => (.«% PACKAGE % % `( % `) ';'» a0 a1 a2 a3)


def «cast:typeIR:typedefIR» : typeIR → typedefIR
  | .VOID  => (.VOID )
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)
  | ._NAME a0 => (._NAME a0)
  | .TYPEDEF a0 a1 => (.TYPEDEF a0 a1)
  | .TYPE a0 a1 => (.TYPE a0 a1)
  | .«LIST `< % `>» a0 => (.«LIST `< % `>» a0)
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)
  | .«ARRAY % `[ % `]» a0 a1 => (.«ARRAY % `[ % `]» a0 a1)
  | .«HEADER_STACK % `[ % `]» a0 a1 => (.«HEADER_STACK % `[ % `]» a0 a1)
  | .«STRUCT % `< % `> `{ % `}» a0 a1 a2 => (.«STRUCT % `< % `> `{ % `}» a0 a1 a2)
  | .«HEADER % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER % `< % `> `{ % `}» a0 a1 a2)
  | .«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2)
  | .«ENUM % `{ % `}» a0 a1 => (.«ENUM % `{ % `}» a0 a1)
  | .«ENUM % `< % `> `{ % `}» a0 a1 a2 => (.«ENUM % `< % `> `{ % `}» a0 a1 a2)
  | .«EXTERN % `< % `> %» a0 a1 a2 => (.«EXTERN % `< % `> %» a0 a1 a2)
  | .«PARSER % `< % `> `( % `)» a0 a1 a2 => (.«PARSER % `< % `> `( % `)» a0 a1 a2)
  | .«CONTROL % `< % `> `( % `)» a0 a1 a2 => (.«CONTROL % `< % `> `( % `)» a0 a1 a2)
  | .«PACKAGE % `< % `> `{ % `}» a0 a1 a2 => (.«PACKAGE % `< % `> `{ % `}» a0 a1 a2)
  | .«TABLE % `{ % `}» a0 a1 => (.«TABLE % `{ % `}» a0 a1)
  | .DEFAULT  => (.DEFAULT )
  | .HEADER_INVALID  => (.HEADER_INVALID )
  | .«SEQ `< % `>» a0 => (.«SEQ `< % `>» a0)
  | .«SEQ `< % ',' '...' `>» a0 => (.«SEQ `< % ',' '...' `>» a0)
  | .«RECORD `{ % `}» a0 => (.«RECORD `{ % `}» a0)
  | .«RECORD `{ % ',' '...' `}» a0 => (.«RECORD `{ % ',' '...' `}» a0)
  | .«SET `< % `>» a0 => (.«SET `< % `>» a0)
  | .«TABLE_ENUM % `{ % `}» a0 a1 => (.«TABLE_ENUM % `{ % `}» a0 a1)
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3 => (.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3)


def «cast:typeIdentifier:name» : typeIdentifier → name
  | ._TID a0 => (._TID a0)


def «cast:typeIdentifier:namedType» : typeIdentifier → namedType
  | ._TID a0 => (._TID a0)


def «cast:typeIdentifier:prefixedTypeName» : typeIdentifier → prefixedTypeName
  | ._TID a0 => (._TID a0)


def «cast:typeIdentifier:type» : typeIdentifier → type
  | ._TID a0 => (._TID a0)


def «cast:typedExpressionIR:argumentIR» : typedExpressionIR → argumentIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)


def «cast:typedExpressionIR:forCollectionExpressionIR» : typedExpressionIR → forCollectionExpressionIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)


def «cast:typedExpressionIR:memberAccessBaseIR» : typedExpressionIR → memberAccessBaseIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)


def «cast:typedExpressionIR:simpleKeysetExpressionIR» : typedExpressionIR → simpleKeysetExpressionIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)


def «cast:typedExpressionIR:switchLabelIR» : typedExpressionIR → switchLabelIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)


def «cast:typedefDeclaration:typeDeclaration» : typedefDeclaration → typeDeclaration
  | .«% TYPEDEF % % ';'» a0 a1 a2 => (.«% TYPEDEF % % ';'» a0 a1 a2)
  | .«% TYPE % % ';'» a0 a1 a2 => (.«% TYPE % % ';'» a0 a1 a2)


def «cast:typedefDeclarationIR:declarationIR» : typedefDeclarationIR → declarationIR
  | .«% TYPEDEF % % ';'» a0 a1 a2 => (.«% TYPEDEF % % ';'» a0 a1 a2)
  | .«% TYPE % % ';'» a0 a1 a2 => (.«% TYPE % % ';'» a0 a1 a2)


def «cast:typedefTypeIR:typeDefIR» : typedefTypeIR → typeDefIR
  | .TYPEDEF a0 a1 => (.TYPEDEF a0 a1)


def «cast:unaryExpression:expression» : unaryExpression → expression
  | .«% %» a0 a1 => (.«% %» a0 a1)


def «cast:unaryExpression:expressionNonBrace» : unaryExpression → expressionNonBrace
  | .«% %» a0 a1 => (.«% %» a0 a1)


def «cast:valueSetDeclaration:parserLocalDeclaration» : valueSetDeclaration → parserLocalDeclaration
  | .«% VALUE_SET `< % `> `( % `) % ';'» a0 a1 a2 a3 => (.«% VALUE_SET `< % `> `( % `) % ';'» a0 a1 a2 a3)


def «cast:valueSetDeclarationIR:parserLocalDeclarationIR» : valueSetDeclarationIR → parserLocalDeclarationIR
  | .«% VALUE_SET `< % `> `( % `) % ';'» a0 a1 a2 a3 => (.«% VALUE_SET `< % `> `( % `) % ';'» a0 a1 a2 a3)


def «cast:valueSetObject:object» : valueSetObject → object
  | .«VALUE_SET `{ % `( % `) `}» a0 a1 => (.«VALUE_SET `{ % `( % `) `}» a0 a1)


def «cast:valueSetType:typeOrVoid» : valueSetType → typeOrVoid
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«INT `< `( % `) `>» a0 => (.«INT `< `( % `) `>» a0)
  | .BIT  => (.BIT )
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«BIT `< `( % `) `>» a0 => (.«BIT `< `( % `) `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)
  | .«VARBIT `< `( % `) `>» a0 => (.«VARBIT `< `( % `) `>» a0)
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:variableDeclaration:blockElementStatement» : variableDeclaration → blockElementStatement
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclaration:controlLocalDeclaration» : variableDeclaration → controlLocalDeclaration
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclaration:parserBlockElementStatement» : variableDeclaration → parserBlockElementStatement
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclaration:parserLocalDeclaration» : variableDeclaration → parserLocalDeclaration
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclarationIR:blockElementStatementIR» : variableDeclarationIR → blockElementStatementIR
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclarationIR:controlLocalDeclarationIR» : variableDeclarationIR → controlLocalDeclarationIR
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclarationIR:parserBlockElementStatementIR» : variableDeclarationIR → parserBlockElementStatementIR
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «cast:variableDeclarationIR:parserLocalDeclarationIR» : variableDeclarationIR → parserLocalDeclarationIR
  | .«% % % % ';'» a0 a1 a2 a3 => (.«% % % % ';'» a0 a1 a2 a3)


def «exec:match:annotation:'@' %» : annotation → Bool
  | .«'@' %» _ => true
  | _ => false

end SpecTec
