import SpecTecDecl0100

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:baseType:valueSetType» : baseType → valueSetType
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


def «cast:baseTypeIR:typeIR» : baseTypeIR → typeIR
  | .VOID  => (.VOID )
  | .BOOL  => (.BOOL )
  | .ERROR  => (.ERROR )
  | .MATCH_KIND  => (.MATCH_KIND )
  | .STRING  => (.STRING )
  | .INT  => (.INT )
  | .«INT `< % `>» a0 => (.«INT `< % `>» a0)
  | .«BIT `< % `>» a0 => (.«BIT `< % `>» a0)
  | .«VARBIT `< % `>» a0 => (.«VARBIT `< % `>» a0)


def «cast:binaryExpression:expression» : binaryExpression → expression
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:blockStatement:statement» : blockStatement → statement
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)


def «cast:blockStatementIR:statementIR» : blockStatementIR → statementIR
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)


def «cast:boolTypeIR:typeIR» : boolTypeIR → typeIR
  | .BOOL  => (.BOOL )


def «cast:boolValue:value» : boolValue → value
  | ._B a0 => (._B a0)


def «cast:booleanLiteral:expressionIR» : booleanLiteral → expressionIR
  | .TRUE  => (.TRUE )
  | .FALSE  => (.FALSE )


def «cast:breakStatement:statementIR» : breakStatement → statementIR
  | .«BREAK ';'»  => (.«BREAK ';'» )


def «cast:builtinIsValidMethodCallee:callee» : builtinIsValidMethodCallee → callee
  | .BUILTIN_IS_VALID a0 => (.BUILTIN_IS_VALID a0)


def «cast:builtinMethodTypeIR:callableTypeIR» : builtinMethodTypeIR → callableTypeIR
  | .BUILTIN_IS_VALID  => (.BUILTIN_IS_VALID )
  | .BUILTIN_SET_VALID  => (.BUILTIN_SET_VALID )
  | .BUILTIN_SET_INVALID  => (.BUILTIN_SET_INVALID )
  | .BUILTIN_PUSH_FRONT  => (.BUILTIN_PUSH_FRONT )
  | .BUILTIN_POP_FRONT  => (.BUILTIN_POP_FRONT )
  | .BUILTIN_SIZE_OF  => (.BUILTIN_SIZE_OF )


def «cast:builtinPopFrontMethodCallee:callee» : builtinPopFrontMethodCallee → callee
  | .BUILTIN_POP_FRONT a0 => (.BUILTIN_POP_FRONT a0)


def «cast:builtinPushFrontMethodCallee:callee» : builtinPushFrontMethodCallee → callee
  | .BUILTIN_PUSH_FRONT a0 => (.BUILTIN_PUSH_FRONT a0)


def «cast:builtinSetInvalidMethodCallee:callee» : builtinSetInvalidMethodCallee → callee
  | .BUILTIN_SET_INVALID a0 => (.BUILTIN_SET_INVALID a0)


def «cast:builtinSetValidMethodCallee:callee» : builtinSetValidMethodCallee → callee
  | .BUILTIN_SET_VALID a0 => (.BUILTIN_SET_VALID a0)


def «cast:builtinSizeMethodCallee:callee» : builtinSizeMethodCallee → callee
  | .BUILTIN_SIZE_OF a0 a1 => (.BUILTIN_SIZE_OF a0 a1)


def «cast:callExpression:expression» : callExpression → expression
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)


def «cast:callExpressionIR:expressionIR» : callExpressionIR → expressionIR
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)


def «cast:callStatement:parserStatement» : callStatement → parserStatement
  | .«% `( % `) ';'» a0 a1 => (.«% `( % `) ';'» a0 a1)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:callStatement:statement» : callStatement → statement
  | .«% `( % `) ';'» a0 a1 => (.«% `( % `) ';'» a0 a1)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:callStatementIR:blockElementStatementIR» : callStatementIR → blockElementStatementIR
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:callStatementIR:parserBlockElementStatementIR» : callStatementIR → parserBlockElementStatementIR
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:callStatementIR:parserStatementIR» : callStatementIR → parserStatementIR
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:callStatementIR:statementIR» : callStatementIR → statementIR
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)


def «cast:castExpression:expression» : castExpression → expression
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)


def «cast:castExpression:expressionNonBrace» : castExpression → expressionNonBrace
  | .«`( % `) %» a0 a1 => (.«`( % `) %» a0 a1)


def «cast:conditionalStatement:statement» : conditionalStatement → statement
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)


def «cast:conditionalStatementIR:statementIR» : conditionalStatementIR → statementIR
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)


def «cast:constantDeclaration:blockElementStatement» : constantDeclaration → blockElementStatement
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclaration:controlLocalDeclaration» : constantDeclaration → controlLocalDeclaration
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclaration:declaration» : constantDeclaration → declaration
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)


def «cast:constantDeclaration:parserBlockElementStatement» : constantDeclaration → parserBlockElementStatement
  | .«% CONST % % % ';'» a0 a1 a2 a3 => (.«% CONST % % % ';'» a0 a1 a2 a3)

end SpecTec
