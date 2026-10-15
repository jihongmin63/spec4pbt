import SpecTecDecl0102

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:emptyStatement:parserStatement» : emptyStatement → parserStatement
  | .«';'»  => (.«';'» )


def «cast:emptyStatement:parserStatementIR» : emptyStatement → parserStatementIR
  | .«';'»  => (.«';'» )


def «cast:emptyStatement:statement» : emptyStatement → statement
  | .«';'»  => (.«';'» )


def «cast:emptyStatement:statementIR» : emptyStatement → statementIR
  | .«';'»  => (.«';'» )


def «cast:enumTypeDeclaration:derivedTypeDeclaration» : enumTypeDeclaration → derivedTypeDeclaration
  | .«% ENUM % `{ % % `}» a0 a1 a2 a3 => (.«% ENUM % `{ % % `}» a0 a1 a2 a3)
  | .«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4 => (.«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4)


def «cast:enumTypeDeclarationIR:declarationIR» : enumTypeDeclarationIR → declarationIR
  | .«% ENUM % `{ % `}» a0 a1 a2 => (.«% ENUM % `{ % `}» a0 a1 a2)
  | .«% ENUM % % `{ % `}» a0 a1 a2 a3 => (.«% ENUM % % `{ % `}» a0 a1 a2 a3)


def «cast:enumTypeIR:typeDefIR» : enumTypeIR → typeDefIR
  | .«ENUM % `{ % `}» a0 a1 => (.«ENUM % `{ % `}» a0 a1)
  | .«ENUM % `< % `> `{ % `}» a0 a1 a2 => (.«ENUM % `< % `> `{ % `}» a0 a1 a2)


def «cast:enumTypeIR:typeIR» : enumTypeIR → typeIR
  | .«ENUM % `{ % `}» a0 a1 => (.«ENUM % `{ % `}» a0 a1)
  | .«ENUM % `< % `> `{ % `}» a0 a1 a2 => (.«ENUM % `< % `> `{ % `}» a0 a1 a2)


def «cast:enumValue:value» : enumValue → value
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% '.' % '.' %» a0 a1 a2 => (.«% '.' % '.' %» a0 a1 a2)


def «cast:errorAccessExpression:accessExpression» : errorAccessExpression → accessExpression
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)


def «cast:errorAccessExpression:expression» : errorAccessExpression → expression
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)


def «cast:errorAccessExpression:expressionNonBrace» : errorAccessExpression → expressionNonBrace
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)


def «cast:errorDeclaration:declaration» : errorDeclaration → declaration
  | .«ERROR `{ % `}» a0 => (.«ERROR `{ % `}» a0)


def «cast:errorValue:value» : errorValue → value
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)


def «cast:exitStatement:statement» : exitStatement → statement
  | .«EXIT ';'»  => (.«EXIT ';'» )


def «cast:exitStatement:statementIR» : exitStatement → statementIR
  | .«EXIT ';'»  => (.«EXIT ';'» )


def «cast:expression:argument» : expression → argument
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expression:callTarget» : expression → callTarget
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expression:expressionList» : expression → expressionList
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expression:memberAccessBase» : expression → memberAccessBase
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expression:simpleKeysetExpression» : expression → simpleKeysetExpression
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expressionList:sequenceOrRecordElementExpression» : expressionList → sequenceOrRecordElementExpression
  | ._EMPTY  => (._EMPTY )
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«'...'»  => (.«'...'» )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)
  | .«% ',' %» a0 a1 => (.«% ',' %» a0 a1)


def «cast:expressionNonBrace:callTargetNonBrace» : expressionNonBrace → callTargetNonBrace
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expressionNonBrace:memberAccessBaseNonBrace» : expressionNonBrace → memberAccessBaseNonBrace
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:expressionNonBrace:switchLabel» : expressionNonBrace → switchLabel
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )
  | .D a0 => (.D a0)
  | .«% W %» a0 a1 => (.«% W %» a0 a1)
  | .«% S %» a0 a1 => (.«% S %» a0 a1)
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)
  | .THIS  => (.THIS )
  | .«% %» a0 a1 => (.«% %» a0 a1)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«`( % `)» a0 => (.«`( % `)» a0)


def «cast:externConstructorPrototype:externConstructorOrMethodPrototype» : externConstructorPrototype → externConstructorOrMethodPrototype
  | .«% % `( % `) ';'» a0 a1 a2 => (.«% % `( % `) ';'» a0 a1 a2)


def «cast:externDeclaration:declaration» : externDeclaration → declaration
  | .«% EXTERN % ';'» a0 a1 => (.«% EXTERN % ';'» a0 a1)
  | .«% EXTERN % % `{ % `}» a0 a1 a2 a3 => (.«% EXTERN % % `{ % `}» a0 a1 a2 a3)


def «cast:externFunctionCallee:callee» : externFunctionCallee → callee
  | .«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» a0 a1 a2 a3 a4 => (.«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» a0 a1 a2 a3 a4)


def «cast:externFunctionDeclaration:externDeclaration» : externFunctionDeclaration → externDeclaration
  | .«% EXTERN % ';'» a0 a1 => (.«% EXTERN % ';'» a0 a1)


def «cast:externFunctionDeclarationIR:declarationIR» : externFunctionDeclarationIR → declarationIR
  | .«% EXTERN % ';'» a0 a1 => (.«% EXTERN % ';'» a0 a1)


def «cast:externFunctionDef:callableDef» : externFunctionDef → callableDef
  | .«EXTERN_FUNCTION % `< % `> `( % `)» a0 a1 a2 => (.«EXTERN_FUNCTION % `< % `> `( % `)» a0 a1 a2)


def «cast:externFunctionTypeDefIR:callableTypeDefIR» : externFunctionTypeDefIR → callableTypeDefIR
  | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)

end SpecTec
