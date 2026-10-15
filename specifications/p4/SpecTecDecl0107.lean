import SpecTecDecl0106

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:prefixedNonTypeName:callTarget» : prefixedNonTypeName → callTarget
  | ._ID a0 => (._ID a0)
  | .APPLY  => (.APPLY )
  | .KEY  => (.KEY )
  | .ACTIONS  => (.ACTIONS )
  | .STATE  => (.STATE )
  | .ENTRIES  => (.ENTRIES )
  | .TYPE  => (.TYPE )
  | .PRIORITY  => (.PRIORITY )
  | .«_ID '.' %» a0 => (.«_ID '.' %» a0)


def «cast:prefixedTypeName:memberAccessBase» : prefixedTypeName → memberAccessBase
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:prefixedTypeName:memberAccessBaseNonBrace» : prefixedTypeName → memberAccessBaseNonBrace
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:prefixedTypeName:namedType» : prefixedTypeName → namedType
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:prefixedTypeName:type» : prefixedTypeName → type
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:prefixedTypeName:valueSetType» : prefixedTypeName → valueSetType
  | ._TID a0 => (._TID a0)
  | .«_TID '.' %» a0 => (.«_TID '.' %» a0)


def «cast:realTypeArgument:realTypeArgumentList» : realTypeArgument → realTypeArgumentList
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


def «cast:realTypeArgument:typeArgument» : realTypeArgument → typeArgument
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


def «cast:recordElementExpression:sequenceOrRecordElementExpression» : recordElementExpression → sequenceOrRecordElementExpression
  | .«% '=' %» a0 a1 => (.«% '=' %» a0 a1)
  | .«% '=' % ',' '...'» a0 a1 => (.«% '=' % ',' '...'» a0 a1)
  | .«% '=' % ',' %» a0 a1 a2 => (.«% '=' % ',' %» a0 a1 a2)
  | .«% '=' % ',' % ',' '...'» a0 a1 a2 => (.«% '=' % ',' % ',' '...'» a0 a1 a2)


def «cast:referenceExpression:expression» : referenceExpression → expression
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


def «cast:referenceExpression:expressionNonBrace» : referenceExpression → expressionNonBrace
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


def «cast:referenceExpression:lvalue» : referenceExpression → lvalue
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


def «cast:rejectTransitionResult:callResult» : rejectTransitionResult → callResult
  | .REJECT a0 => (.REJECT a0)


def «cast:rejectTransitionResult:expressionResult» : rejectTransitionResult → expressionResult
  | .REJECT a0 => (.REJECT a0)


def «cast:rejectTransitionResult:parserStatementResult» : rejectTransitionResult → parserStatementResult
  | .REJECT a0 => (.REJECT a0)


def «cast:rejectTransitionResult:selectCaseMatchResult» : rejectTransitionResult → selectCaseMatchResult
  | .REJECT a0 => (.REJECT a0)


def «cast:rejectTransitionResult:storageReferenceResult» : rejectTransitionResult → storageReferenceResult
  | .REJECT a0 => (.REJECT a0)


def «cast:rejectTransitionResult:transitionResult» : rejectTransitionResult → transitionResult
  | .REJECT a0 => (.REJECT a0)


def «cast:returnResult:callResult» : returnResult → callResult
  | .RETURN a0 => (.RETURN a0)


def «cast:returnResult:definedFunctionResult» : returnResult → definedFunctionResult
  | .RETURN a0 => (.RETURN a0)


def «cast:returnResult:statementResult» : returnResult → statementResult
  | .RETURN a0 => (.RETURN a0)


def «cast:returnStatement:statement» : returnStatement → statement
  | .«RETURN ';'»  => (.«RETURN ';'» )
  | .«RETURN % ';'» a0 => (.«RETURN % ';'» a0)


def «cast:returnStatementIR:statementIR» : returnStatementIR → statementIR
  | .«RETURN ';'»  => (.«RETURN ';'» )
  | .«RETURN % ';'» a0 => (.«RETURN % ';'» a0)


def «cast:selectExpression:stateExpression» : selectExpression → stateExpression
  | .«SELECT `( % `) `{ % `}» a0 a1 => (.«SELECT `( % `) `{ % `}» a0 a1)


def «cast:selectExpressionIR:stateExpressionIR» : selectExpressionIR → stateExpressionIR
  | .«SELECT `( % `) `{ % `}» a0 a1 => (.«SELECT `( % `) `{ % `}» a0 a1)


def «cast:sequenceTypeIR:typeIR» : sequenceTypeIR → typeIR
  | .«SEQ `< % `>» a0 => (.«SEQ `< % `>» a0)
  | .«SEQ `< % ',' '...' `>» a0 => (.«SEQ `< % ',' '...' `>» a0)


def «cast:sequenceValue:value» : sequenceValue → value
  | .«SEQ `( % `)» a0 => (.«SEQ `( % `)» a0)
  | .«SEQ `( % ',' '...' `)» a0 => (.«SEQ `( % ',' '...' `)» a0)


def «cast:serializableEnumTypeIR:typeIR» : serializableEnumTypeIR → typeIR
  | .«ENUM % `< % `> `{ % `}» a0 a1 a2 => (.«ENUM % `< % `> `{ % `}» a0 a1 a2)


def «cast:simpleKeysetExpression:keysetExpression» : simpleKeysetExpression → keysetExpression
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
  | .«% '&&&' %» a0 a1 => (.«% '&&&' %» a0 a1)
  | .«% '..' %» a0 a1 => (.«% '..' %» a0 a1)
  | .DEFAULT  => (.DEFAULT )
  | .«'_'»  => (.«'_'» )


def «cast:simpleKeysetExpression:simpleKeysetExpressionList» : simpleKeysetExpression → simpleKeysetExpressionList
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
  | .«% '&&&' %» a0 a1 => (.«% '&&&' %» a0 a1)
  | .«% '..' %» a0 a1 => (.«% '..' %» a0 a1)
  | .DEFAULT  => (.DEFAULT )
  | .«'_'»  => (.«'_'» )


def «cast:simpleKeysetExpressionIR:keysetExpressionIR» : simpleKeysetExpressionIR → keysetExpressionIR
  | .«% '#' %» a0 a1 => (.«% '#' %» a0 a1)
  | .«% '&&&' %» a0 a1 => (.«% '&&&' %» a0 a1)
  | .«% '..' %» a0 a1 => (.«% '..' %» a0 a1)
  | .DEFAULT  => (.DEFAULT )
  | .«'_'»  => (.«'_'» )


def «cast:sliceAccessExpression:accessExpression» : sliceAccessExpression → accessExpression
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)

end SpecTec
