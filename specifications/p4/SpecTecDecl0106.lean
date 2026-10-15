import SpecTecDecl0105

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:nonTypeName:expression» : nonTypeName → expression
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:nonTypeName:lvalue» : nonTypeName → lvalue
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:nonTypeName:memberAccessBase» : nonTypeName → memberAccessBase
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:nonTypeName:name» : nonTypeName → name
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:nonTypeName:prefixedNonTypeName» : nonTypeName → prefixedNonTypeName
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:nonTypeName:referenceExpression» : nonTypeName → referenceExpression
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )


def «cast:packageObjectTypeDefIR:typeDefIR» : packageObjectTypeDefIR → typeDefIR
  | .«PACKAGE % `< % ',' % `> `{ % `}» a0 a1 a2 a3 => (.«PACKAGE % `< % ',' % `> `{ % `}» a0 a1 a2 a3)


def «cast:packageObjectTypeIR:typeIR» : packageObjectTypeIR → typeIR
  | .«PACKAGE % `< % `> `{ % `}» a0 a1 a2 => (.«PACKAGE % `< % `> `{ % `}» a0 a1 a2)


def «cast:packageTypeDeclaration:typeDeclaration» : packageTypeDeclaration → typeDeclaration
  | .«% PACKAGE % % `( % `) ';'» a0 a1 a2 a3 => (.«% PACKAGE % % `( % `) ';'» a0 a1 a2 a3)


def «cast:packageTypeDeclarationIR:declarationIR» : packageTypeDeclarationIR → declarationIR
  | .«% PACKAGE % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4 => (.«% PACKAGE % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4)


def «cast:parameter:nonEmptyParameterList» : parameter → nonEmptyParameterList
  | .«% % % % %» a0 a1 a2 a3 a4 => (.«% % % % %» a0 a1 a2 a3 a4)


def «cast:parenthesizedExpression:expression» : parenthesizedExpression → expression
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:parenthesizedExpression:expressionNonBrace» : parenthesizedExpression → expressionNonBrace
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:parserApplyMethodCallee:callee» : parserApplyMethodCallee → callee
  | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6 => (.«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6)


def «cast:parserApplyMethodTypeIR:callableTypeDefIR» : parserApplyMethodTypeIR → callableTypeDefIR
  | .«PARSER_APPLY `( % `)» a0 => (.«PARSER_APPLY `( % `)» a0)


def «cast:parserApplyMethodTypeIR:callableTypeIR» : parserApplyMethodTypeIR → callableTypeIR
  | .«PARSER_APPLY `( % `)» a0 => (.«PARSER_APPLY `( % `)» a0)


def «cast:parserBlockStatement:parserStatement» : parserBlockStatement → parserStatement
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)


def «cast:parserBlockStatementIR:parserStatementIR» : parserBlockStatementIR → parserStatementIR
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)


def «cast:parserConditionalStatement:parserStatement» : parserConditionalStatement → parserStatement
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)


def «cast:parserDeclaration:declaration» : parserDeclaration → declaration
  | .«% PARSER % % `( % `) % `{ % % `}» a0 a1 a2 a3 a4 a5 a6 => (.«% PARSER % % `( % `) % `{ % % `}» a0 a1 a2 a3 a4 a5 a6)


def «cast:parserDeclarationIR:declarationIR» : parserDeclarationIR → declarationIR
  | .«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» a0 a1 a2 a3 a4 a5 a6 a7 => (.«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» a0 a1 a2 a3 a4 a5 a6 a7)


def «cast:parserObjectTypeDefIR:typeDefIR» : parserObjectTypeDefIR → typeDefIR
  | .«PARSER % `< % ',' % `> `( % `)» a0 a1 a2 a3 => (.«PARSER % `< % ',' % `> `( % `)» a0 a1 a2 a3)


def «cast:parserObjectTypeIR:typeIR» : parserObjectTypeIR → typeIR
  | .«PARSER % `< % `> `( % `)» a0 a1 a2 => (.«PARSER % `< % `> `( % `)» a0 a1 a2)


def «cast:parserState:parserStateList» : parserState → parserStateList
  | .«% STATE % `{ % % `}» a0 a1 a2 a3 => (.«% STATE % `{ % % `}» a0 a1 a2 a3)


def «cast:parserStatement:parserBlockElementStatement» : parserStatement → parserBlockElementStatement
  | .«';'»  => (.«';'» )
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)
  | .«% `( % `) ';'» a0 a1 => (.«% `( % `) ';'» a0 a1)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)


def «cast:parserStatementIR:parserBlockElementStatementIR» : parserStatementIR → parserBlockElementStatementIR
  | .«';'»  => (.«';'» )
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)


def «cast:parserTypeDeclaration:typeDeclaration» : parserTypeDeclaration → typeDeclaration
  | .«% PARSER % % `( % `) ';'» a0 a1 a2 a3 => (.«% PARSER % % `( % `) ';'» a0 a1 a2 a3)


def «cast:parserTypeDeclarationIR:declarationIR» : parserTypeDeclarationIR → declarationIR
  | .«% PARSER % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4 => (.«% PARSER % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4)


def «cast:prefixedNameIR:callableTargetIR» : prefixedNameIR → callableTargetIR
  | ._BARE a0 => (._BARE a0)
  | .«'.' %» a0 => (.«'.' %» a0)


def «cast:prefixedNameIR:expressionIR» : prefixedNameIR → expressionIR
  | ._BARE a0 => (._BARE a0)
  | .«'.' %» a0 => (.«'.' %» a0)


def «cast:prefixedNameIR:lvalueIR» : prefixedNameIR → lvalueIR
  | ._BARE a0 => (._BARE a0)
  | .«'.' %» a0 => (.«'.' %» a0)


def «cast:prefixedNameIR:storageReference» : prefixedNameIR → storageReference
  | ._BARE a0 => (._BARE a0)
  | .«'.' %» a0 => (.«'.' %» a0)

end SpecTec
