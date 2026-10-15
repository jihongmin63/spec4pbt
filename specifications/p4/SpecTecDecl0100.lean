import SpecTecDecl0099

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:abortResult:calleeResult» : abortResult → calleeResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:copyInArgumentResult» : abortResult → copyInArgumentResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:copyInResult» : abortResult → copyInResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:declarationResult» : abortResult → declarationResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:expressionListResult» : abortResult → expressionListResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:expressionResult» : abortResult → expressionResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:keysetExpressionResult» : abortResult → keysetExpressionResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:simpleKeysetExpressionResult» : abortResult → simpleKeysetExpressionResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:statementResult» : abortResult → statementResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:abortResult:storageReferenceResult» : abortResult → storageReferenceResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:accessExpression:expression» : accessExpression → expression
  | .«ERROR '.' %» a0 => (.«ERROR '.' %» a0)
  | .«% '.' %» a0 a1 => (.«% '.' %» a0 a1)
  | .«% `[ % `]» a0 a1 => (.«% `[ % `]» a0 a1)
  | .«% `[ % % % `]» a0 a1 a2 a3 => (.«% `[ % % % `]» a0 a1 a2 a3)


def «cast:actionCallee:callee» : actionCallee → callee
  | .«ACTION % '.' % `( % '#' % `) %» a0 a1 a2 a3 a4 => (.«ACTION % '.' % `( % '#' % `) %» a0 a1 a2 a3 a4)


def «cast:actionDeclaration:controlLocalDeclaration» : actionDeclaration → controlLocalDeclaration
  | .«% ACTION % `( % `) %» a0 a1 a2 a3 => (.«% ACTION % `( % `) %» a0 a1 a2 a3)


def «cast:actionDeclaration:declaration» : actionDeclaration → declaration
  | .«% ACTION % `( % `) %» a0 a1 a2 a3 => (.«% ACTION % `( % `) %» a0 a1 a2 a3)


def «cast:actionDeclarationIR:controlLocalDeclarationIR» : actionDeclarationIR → controlLocalDeclarationIR
  | .«% ACTION % `( % `) %» a0 a1 a2 a3 => (.«% ACTION % `( % `) %» a0 a1 a2 a3)


def «cast:actionDeclarationIR:declarationIR» : actionDeclarationIR → declarationIR
  | .«% ACTION % `( % `) %» a0 a1 a2 a3 => (.«% ACTION % `( % `) %» a0 a1 a2 a3)


def «cast:actionDef:callableDef» : actionDef → callableDef
  | .«% ACTION % `( % `) %» a0 a1 a2 a3 => (.«% ACTION % `( % `) %» a0 a1 a2 a3)


def «cast:actionTypeIR:callableTypeDefIR» : actionTypeIR → callableTypeDefIR
  | .«% ACTION % `( % `)» a0 a1 a2 => (.«% ACTION % `( % `)» a0 a1 a2)


def «cast:actionTypeIR:callableTypeIR» : actionTypeIR → callableTypeIR
  | .«% ACTION % `( % `)» a0 a1 a2 => (.«% ACTION % `( % `)» a0 a1 a2)


def «cast:aliasTypeIR:typeDefIR» : aliasTypeIR → typeDefIR
  | .TYPEDEF a0 a1 => (.TYPEDEF a0 a1)
  | .TYPE a0 a1 => (.TYPE a0 a1)


def «cast:aliasTypeIR:typeIR» : aliasTypeIR → typeIR
  | .TYPEDEF a0 a1 => (.TYPEDEF a0 a1)
  | .TYPE a0 a1 => (.TYPE a0 a1)


def «cast:annotation:annotationList» : annotation → annotationList
  | .«'@' %» a0 => (.«'@' %» a0)
  | .«'@' % `( % `)» a0 a1 => (.«'@' % `( % `)» a0 a1)
  | .«'@' % `[ % `]» a0 a1 => (.«'@' % `[ % `]» a0 a1)
  | .«'@' PRAGMA % %» a0 a1 => (.«'@' PRAGMA % %» a0 a1)


def «cast:annotationListNonEmpty:annotationList» : annotationListNonEmpty → annotationList
  | .«'@' %» a0 => (.«'@' %» a0)
  | .«'@' % `( % `)» a0 a1 => (.«'@' % `( % `)» a0 a1)
  | .«'@' % `[ % `]» a0 a1 => (.«'@' % `[ % `]» a0 a1)
  | .«'@' PRAGMA % %» a0 a1 => (.«'@' PRAGMA % %» a0 a1)
  | .«% %» a0 a1 => (.«% %» a0 a1)


def «cast:argument:argumentListNonEmpty» : argument → argumentListNonEmpty
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
  | .«% '=' %» a0 a1 => (.«% '=' %» a0 a1)
  | .«% '=' '_'» a0 => (.«% '=' '_'» a0)
  | .«'_'»  => (.«'_'» )


def «cast:argumentListNonEmpty:argumentList» : argumentListNonEmpty → argumentList
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
  | .«% '=' %» a0 a1 => (.«% '=' %» a0 a1)
  | .«% '=' '_'» a0 => (.«% '=' '_'» a0)
  | .«'_'»  => (.«'_'» )
  | .«% ',' %» a0 a1 => (.«% ',' %» a0 a1)


def «cast:arrayTypeIR:typeIR» : arrayTypeIR → typeIR
  | .«ARRAY % `[ % `]» a0 a1 => (.«ARRAY % `[ % `]» a0 a1)


def «cast:arrayValue:value» : arrayValue → value
  | .«ARRAY `[ % `]» a0 => (.«ARRAY `[ % `]» a0)


def «cast:assignmentStatement:parserStatement» : assignmentStatement → parserStatement
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)


def «cast:assignmentStatement:statement» : assignmentStatement → statement
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)


def «cast:assignmentStatementIR:parserStatementIR» : assignmentStatementIR → parserStatementIR
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)


def «cast:assignmentStatementIR:statementIR» : assignmentStatementIR → statementIR
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)


def «cast:baseType:type» : baseType → type
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

end SpecTec
