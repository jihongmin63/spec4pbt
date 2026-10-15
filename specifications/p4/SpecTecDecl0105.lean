import SpecTecDecl0104

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:headerValue:value» : headerValue → value
  | .«HEADER % `{ % ';' % `}» a0 a1 a2 => (.«HEADER % `{ % ';' % `}» a0 a1 a2)


def «cast:identifier:tableCustomName» : identifier → tableCustomName
  | ._ID a0 => (._ID a0)


def «cast:indexAccessExpression:accessExpression» : indexAccessExpression → accessExpression
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)


def «cast:initializer:initializerOpt» : initializer → initializerOpt
  | .«'=' %» a0 => (.«'=' %» a0)


def «cast:instantiation:controlLocalDeclaration» : instantiation → controlLocalDeclaration
  | .«% % `( % `) % ';'» a0 a1 a2 a3 => (.«% % `( % `) % ';'» a0 a1 a2 a3)
  | .«% % `( % `) % % ';'» a0 a1 a2 a3 a4 => (.«% % `( % `) % % ';'» a0 a1 a2 a3 a4)


def «cast:instantiation:declaration» : instantiation → declaration
  | .«% % `( % `) % ';'» a0 a1 a2 a3 => (.«% % `( % `) % ';'» a0 a1 a2 a3)
  | .«% % `( % `) % % ';'» a0 a1 a2 a3 a4 => (.«% % `( % `) % % ';'» a0 a1 a2 a3 a4)


def «cast:instantiation:objectDeclaration» : instantiation → objectDeclaration
  | .«% % `( % `) % ';'» a0 a1 a2 a3 => (.«% % `( % `) % ';'» a0 a1 a2 a3)
  | .«% % `( % `) % % ';'» a0 a1 a2 a3 a4 => (.«% % `( % `) % % ';'» a0 a1 a2 a3 a4)


def «cast:instantiation:parserLocalDeclaration» : instantiation → parserLocalDeclaration
  | .«% % `( % `) % ';'» a0 a1 a2 a3 => (.«% % `( % `) % ';'» a0 a1 a2 a3)
  | .«% % `( % `) % % ';'» a0 a1 a2 a3 a4 => (.«% % `( % `) % % ';'» a0 a1 a2 a3 a4)


def «cast:instantiationIR:controlLocalDeclarationIR» : instantiationIR → controlLocalDeclarationIR
  | .«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5 => (.«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5)


def «cast:instantiationIR:declarationIR» : instantiationIR → declarationIR
  | .«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5 => (.«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5)


def «cast:instantiationIR:objectDeclarationIR» : instantiationIR → objectDeclarationIR
  | .«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5 => (.«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5)


def «cast:instantiationIR:parserLocalDeclarationIR» : instantiationIR → parserLocalDeclarationIR
  | .«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5 => (.«% % % `( % `) % % ';'» a0 a1 a2 a3 a4 a5)


def «cast:integerLiteral:integerValue» : integerLiteral → integerValue
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)


def «cast:integerLiteral:value» : integerLiteral → value
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)


def «cast:integerValue:value» : integerValue → value
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«% '.' % V %» a0 a1 a2 => (.«% '.' % V %» a0 a1 a2)


def «cast:listTypeIR:typeIR» : listTypeIR → typeIR
  | .«LIST `< % `>» a0 => (.«LIST `< % `>» a0)


def «cast:literalExpression:expression» : literalExpression → expression
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)


def «cast:literalExpression:expressionIR» : literalExpression → expressionIR
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)


def «cast:literalExpression:expressionNonBrace» : literalExpression → expressionNonBrace
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)


def «cast:matchKindDeclaration:declaration» : matchKindDeclaration → declaration
  | .«MATCH_KIND `{ % % `}» a0 a1 => (.«MATCH_KIND `{ % % `}» a0 a1)


def «cast:memberAccessExpression:accessExpression» : memberAccessExpression → accessExpression
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)


def «cast:methodTypeIR:callableTypeIR» : methodTypeIR → callableTypeIR
  | .BUILTIN_IS_VALID  => (.BUILTIN_IS_VALID )
  | .BUILTIN_SET_VALID  => (.BUILTIN_SET_VALID )
  | .BUILTIN_SET_INVALID  => (.BUILTIN_SET_INVALID )
  | .BUILTIN_PUSH_FRONT  => (.BUILTIN_PUSH_FRONT )
  | .BUILTIN_POP_FRONT  => (.BUILTIN_POP_FRONT )
  | .BUILTIN_SIZE_OF  => (.BUILTIN_SIZE_OF )
  | .«EXTERN_METHOD % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_METHOD % `( % `) ':' %» a0 a1 a2)
  | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» a0 a1 a2)
  | .«PARSER_APPLY `( % `)» a0 => (.«PARSER_APPLY `( % `)» a0)
  | .«CONTROL_APPLY `( % `)» a0 => (.«CONTROL_APPLY `( % `)» a0)
  | .«TABLE_APPLY ':' %» a0 => (.«TABLE_APPLY ':' %» a0)


def «cast:name:nameList» : name → nameList
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | ._TID a0 => (._TID a0)
  | .LIST  => (.LIST )


def «cast:name:typeParameterList» : name → typeParameterList
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | ._TID a0 => (._TID a0)
  | .LIST  => (.LIST )


def «cast:nameTypeIR:typeIR» : nameTypeIR → typeIR
  | ._NAME a0 => (._NAME a0)


def «cast:namedExpression:namedExpressionList» : namedExpression → namedExpressionList
  | .«% '=' %» a0 a1 => (.«% '=' %» a0 a1)


def «cast:namedType:callTarget» : namedType → callTarget
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)


def «cast:namedType:callTargetNonBrace» : namedType → callTargetNonBrace
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)


def «cast:namedType:type» : namedType → type
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)
  | .«% `< % `>» a0 a1 => (.«% `< % `>» a0 a1)


def «cast:newTypeIR:typeDefIR» : newTypeIR → typeDefIR
  | .TYPE a0 a1 => (.TYPE a0 a1)


def «cast:newTypeIR:typeIR» : newTypeIR → typeIR
  | .TYPE a0 a1 => (.TYPE a0 a1)


def «cast:nonEmptyParameterList:parameterList» : nonEmptyParameterList → parameterList
  | .«% % % % %» a0 a1 a2 a3 a4 => (.«% % % % %» a0 a1 a2 a3 a4)
  | .«% ',' %» a0 a1 => (.«% ',' %» a0 a1)

end SpecTec
