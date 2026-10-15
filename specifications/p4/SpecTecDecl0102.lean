import SpecTecDecl0101

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:constantDeclaration:parserLocalDeclaration» : constantDeclaration → parserLocalDeclaration
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclarationIR:blockElementStatementIR» : constantDeclarationIR → blockElementStatementIR
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclarationIR:controlLocalDeclarationIR» : constantDeclarationIR → controlLocalDeclarationIR
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclarationIR:declarationIR» : constantDeclarationIR → declarationIR
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclarationIR:parserBlockElementStatementIR» : constantDeclarationIR → parserBlockElementStatementIR
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclarationIR:parserLocalDeclarationIR» : constantDeclarationIR → parserLocalDeclarationIR
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:continueStatement:statementIR» : continueStatement → statementIR
  | .«CONTINUE ';'»  => (.«CONTINUE ';'» )


def «cast:controlApplyMethodCallee:callee» : controlApplyMethodCallee → callee
  | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6 a7 => (.«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6 a7)


def «cast:controlApplyMethodTypeIR:callableTypeDefIR» : controlApplyMethodTypeIR → callableTypeDefIR
  | .«CONTROL_APPLY `( % `)» a0 => (.«CONTROL_APPLY `( % `)» a0)


def «cast:controlApplyMethodTypeIR:callableTypeIR» : controlApplyMethodTypeIR → callableTypeIR
  | .«CONTROL_APPLY `( % `)» a0 => (.«CONTROL_APPLY `( % `)» a0)


def «cast:controlDeclaration:declaration» : controlDeclaration → declaration
  | .«% CONTROL % % `( % `) % `{ % APPLY % `}» a0 a1 a2 a3 a4 a5 a6 => (.«% CONTROL % % `( % `) % `{ % APPLY % `}» a0 a1 a2 a3 a4 a5 a6)


def «cast:controlDeclarationIR:declarationIR» : controlDeclarationIR → declarationIR
  | .«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» a0 a1 a2 a3 a4 a5 a6 a7 => (.«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» a0 a1 a2 a3 a4 a5 a6 a7)


def «cast:controlObjectTypeDefIR:typeDefIR» : controlObjectTypeDefIR → typeDefIR
  | .«CONTROL % `< % ',' % `> `( % `)» a0 a1 a2 a3 => (.«CONTROL % `< % ',' % `> `( % `)» a0 a1 a2 a3)


def «cast:controlObjectTypeIR:typeIR» : controlObjectTypeIR → typeIR
  | .«CONTROL % `< % `> `( % `)» a0 a1 a2 => (.«CONTROL % `< % `> `( % `)» a0 a1 a2)


def «cast:controlTypeDeclaration:typeDeclaration» : controlTypeDeclaration → typeDeclaration
  | .«% CONTROL % % `( % `) ';'» a0 a1 a2 a3 => (.«% CONTROL % % `( % `) ';'» a0 a1 a2 a3)


def «cast:controlTypeDeclarationIR:declarationIR» : controlTypeDeclarationIR → declarationIR
  | .«% CONTROL % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4 => (.«% CONTROL % `< % ',' % `> `( % `) ';'» a0 a1 a2 a3 a4)


def «cast:dataExpression:expression» : dataExpression → expression
  | .«'{#}'»  => (.«'{#}'» )
  | .«`{ % % `}» a0 a1 => (.«`{ % % `}» a0 a1)


def «cast:declarationResult:statementResult» : declarationResult → statementResult
  | ._EMPTY  => (._EMPTY )
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)


def «cast:defaultExpression:expression» : defaultExpression → expression
  | .«'...'»  => (.«'...'» )


def «cast:definedFunctionCallee:callee» : definedFunctionCallee → callee
  | .«FUNCTION % `< % `> `( % '#' % `) %» a0 a1 a2 a3 a4 => (.«FUNCTION % `< % `> `( % '#' % `) %» a0 a1 a2 a3 a4)


def «cast:definedFunctionDef:callableDef» : definedFunctionDef → callableDef
  | .«FUNCTION % `< % `> `( % `) %» a0 a1 a2 a3 => (.«FUNCTION % `< % `> `( % `) %» a0 a1 a2 a3)


def «cast:definedFunctionResult:callResult» : definedFunctionResult → callResult
  | .EXIT  => (.EXIT )
  | .RETURN a0 => (.RETURN a0)


def «cast:definedFunctionTypeDefIR:callableTypeDefIR» : definedFunctionTypeDefIR → callableTypeDefIR
  | .«FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)


def «cast:derivedTypeDeclaration:declaration» : derivedTypeDeclaration → declaration
  | .«% ENUM % `{ % % `}» a0 a1 a2 a3 => (.«% ENUM % `{ % % `}» a0 a1 a2 a3)
  | .«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4 => (.«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4)
  | .«% STRUCT % % `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3)


def «cast:derivedTypeDeclaration:typeDeclaration» : derivedTypeDeclaration → typeDeclaration
  | .«% ENUM % `{ % % `}» a0 a1 a2 a3 => (.«% ENUM % `{ % % `}» a0 a1 a2 a3)
  | .«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4 => (.«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4)
  | .«% STRUCT % % `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3)


def «cast:derivedTypeDeclaration:typedef» : derivedTypeDeclaration → typedef
  | .«% ENUM % `{ % % `}» a0 a1 a2 a3 => (.«% ENUM % `{ % % `}» a0 a1 a2 a3)
  | .«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4 => (.«% ENUM % % `{ % % `}» a0 a1 a2 a3 a4)
  | .«% STRUCT % % `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER % % `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3)


def «cast:derivedTypeDeclarationIR:declarationIR» : derivedTypeDeclarationIR → declarationIR
  | .«% ENUM % `{ % `}» a0 a1 a2 => (.«% ENUM % `{ % `}» a0 a1 a2)
  | .«% ENUM % % `{ % `}» a0 a1 a2 a3 => (.«% ENUM % % `{ % `}» a0 a1 a2 a3)
  | .«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3)


def «cast:derivedTypeDeclarationIR:typedefIR» : derivedTypeDeclarationIR → typedefIR
  | .«% ENUM % `{ % `}» a0 a1 a2 => (.«% ENUM % `{ % `}» a0 a1 a2)
  | .«% ENUM % % `{ % `}» a0 a1 a2 a3 => (.«% ENUM % % `{ % `}» a0 a1 a2 a3)
  | .«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3)
  | .«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3)
  | .«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3)


def «cast:directApplicationStatement:parserStatement» : directApplicationStatement → parserStatement
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)


def «cast:directApplicationStatement:statement» : directApplicationStatement → statement
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)


def «cast:directApplicationStatementIR:parserStatementIR» : directApplicationStatementIR → parserStatementIR
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)


def «cast:directApplicationStatementIR:statementIR» : directApplicationStatementIR → statementIR
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)

end SpecTec
