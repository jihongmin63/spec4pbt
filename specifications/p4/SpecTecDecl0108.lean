import SpecTecDecl0107

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:statement:blockElementStatement» : statement → blockElementStatement
  | .«';'»  => (.«';'» )
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)
  | .«% `( % `) ';'» a0 a1 => (.«% `( % `) ';'» a0 a1)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)
  | .«RETURN ';'»  => (.«RETURN ';'» )
  | .«RETURN % ';'» a0 => (.«RETURN % ';'» a0)
  | .«EXIT ';'»  => (.«EXIT ';'» )
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)
  | .«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5 => (.«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5)
  | .«BREAK ';'»  => (.«BREAK ';'» )
  | .«CONTINUE ';'»  => (.«CONTINUE ';'» )
  | .«SWITCH `( % `) `{ % `}» a0 a1 => (.«SWITCH `( % `) `{ % `}» a0 a1)


def «cast:statementIR:blockElementStatementIR» : statementIR → blockElementStatementIR
  | .«';'»  => (.«';'» )
  | .«% % % ';'» a0 a1 a2 => (.«% % % ';'» a0 a1 a2)
  | .«% `< % `> `( % `) ';'» a0 a1 a2 => (.«% `< % `> `( % `) ';'» a0 a1 a2)
  | .«% '.' APPLY `( % `) ';'» a0 a1 => (.«% '.' APPLY `( % `) ';'» a0 a1)
  | .«RETURN ';'»  => (.«RETURN ';'» )
  | .«RETURN % ';'» a0 => (.«RETURN % ';'» a0)
  | .«EXIT ';'»  => (.«EXIT ';'» )
  | .«% `{ % `}» a0 a1 => (.«% `{ % `}» a0 a1)
  | .«IF `( % `) %» a0 a1 => (.«IF `( % `) %» a0 a1)
  | .«IF `( % `) % ELSE %» a0 a1 a2 => (.«IF `( % `) % ELSE %» a0 a1 a2)
  | .«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5 => (.«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5)
  | .«BREAK ';'»  => (.«BREAK ';'» )
  | .«CONTINUE ';'»  => (.«CONTINUE ';'» )
  | .«SWITCH `( % `) `{ % `}» a0 a1 => (.«SWITCH `( % `) `{ % `}» a0 a1)


def «cast:stringLiteral:expressionIR» : stringLiteral → expressionIR
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)


def «cast:stringLiteral:value» : stringLiteral → value
  | .«'"' % '"'» a0 => (.«'"' % '"'» a0)


def «cast:structTypeDeclaration:derivedTypeDeclaration» : structTypeDeclaration → derivedTypeDeclaration
  | .«% STRUCT % % `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % % `{ % `}» a0 a1 a2 a3)


def «cast:structTypeDeclarationIR:declarationIR» : structTypeDeclarationIR → declarationIR
  | .«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% STRUCT % `< % `> `{ % `}» a0 a1 a2 a3)


def «cast:structTypeDefIR:typeDefIR» : structTypeDefIR → typeDefIR
  | .«STRUCT % `< % `> `{ % `}» a0 a1 a2 => (.«STRUCT % `< % `> `{ % `}» a0 a1 a2)


def «cast:structTypeIR:typeIR» : structTypeIR → typeIR
  | .«STRUCT % `< % `> `{ % `}» a0 a1 a2 => (.«STRUCT % `< % `> `{ % `}» a0 a1 a2)


def «cast:structValue:value» : structValue → value
  | .«STRUCT % `{ % `}» a0 a1 => (.«STRUCT % `{ % `}» a0 a1)


def «cast:switchStatement:statement» : switchStatement → statement
  | .«SWITCH `( % `) `{ % `}» a0 a1 => (.«SWITCH `( % `) `{ % `}» a0 a1)


def «cast:switchStatementIR:statementIR» : switchStatementIR → statementIR
  | .«SWITCH `( % `) `{ % `}» a0 a1 => (.«SWITCH `( % `) `{ % `}» a0 a1)


def «cast:tableActionsPropertyIR:tablePropertyIR» : tableActionsPropertyIR → tablePropertyIR
  | .«ACTIONS '=' `{ % `}» a0 => (.«ACTIONS '=' `{ % `}» a0)


def «cast:tableApplyMethodCallee:callee» : tableApplyMethodCallee → callee
  | .«TABLE % '.' APPLY `{ % ';' % `}» a0 a1 a2 => (.«TABLE % '.' APPLY `{ % ';' % `}» a0 a1 a2)


def «cast:tableApplyMethodTypeIR:callableTypeIR» : tableApplyMethodTypeIR → callableTypeIR
  | .«TABLE_APPLY ':' %» a0 => (.«TABLE_APPLY ':' %» a0)


def «cast:tableCustomPropertyIR:tablePropertyIR» : tableCustomPropertyIR → tablePropertyIR
  | .«% % CUSTOM % % ';'» a0 a1 a2 a3 => (.«% % CUSTOM % % ';'» a0 a1 a2 a3)
  | .«% % CUSTOM_CONST % % ';'» a0 a1 a2 a3 => (.«% % CUSTOM_CONST % % ';'» a0 a1 a2 a3)


def «cast:tableDeclaration:controlLocalDeclaration» : tableDeclaration → controlLocalDeclaration
  | .«% TABLE % `{ % `}» a0 a1 a2 => (.«% TABLE % `{ % `}» a0 a1 a2)


def «cast:tableDeclarationIR:controlLocalDeclarationIR» : tableDeclarationIR → controlLocalDeclarationIR
  | .«% TABLE % % `{ % `}» a0 a1 a2 a3 => (.«% TABLE % % `{ % `}» a0 a1 a2 a3)


def «cast:tableDefaultActionPropertyIR:tablePropertyIR» : tableDefaultActionPropertyIR → tablePropertyIR
  | .«% % DEFAULT_ACTION '=' % ';'» a0 a1 a2 => (.«% % DEFAULT_ACTION '=' % ';'» a0 a1 a2)


def «cast:tableEntriesPropertyIR:tablePropertyIR» : tableEntriesPropertyIR → tablePropertyIR
  | .«% % ENTRIES '=' `{ % `}» a0 a1 a2 => (.«% % ENTRIES '=' `{ % `}» a0 a1 a2)


def «cast:tableKeysPropertyIR:tablePropertyIR» : tableKeysPropertyIR → tablePropertyIR
  | .«KEY '=' `{ % `}» a0 => (.«KEY '=' `{ % `}» a0)


def «cast:tableMetadataEnumTypeIR:typeIR» : tableMetadataEnumTypeIR → typeIR
  | .«TABLE_ENUM % `{ % `}» a0 a1 => (.«TABLE_ENUM % `{ % `}» a0 a1)


def «cast:tableMetadataEnumValue:value» : tableMetadataEnumValue → value
  | .«TABLE_ENUM % '.' %» a0 a1 => (.«TABLE_ENUM % '.' %» a0 a1)


def «cast:tableMetadataStructTypeIR:typeIR» : tableMetadataStructTypeIR → typeIR
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3 => (.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3)


def «cast:tableMetadataStructValue:value» : tableMetadataStructValue → value
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3 => (.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3)


def «cast:tableMetadataTypeIR:typeIR» : tableMetadataTypeIR → typeIR
  | .«TABLE_ENUM % `{ % `}» a0 a1 => (.«TABLE_ENUM % `{ % `}» a0 a1)
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3 => (.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» a0 a1 a2 a3)


def «cast:tableObjectTypeIR:typeIR» : tableObjectTypeIR → typeIR
  | .«TABLE % `{ % `}» a0 a1 => (.«TABLE % `{ % `}» a0 a1)


def «cast:ternaryExpression:expression» : ternaryExpression → expression
  | .«% '?' % ':' %» a0 a1 a2 => (.«% '?' % ':' %» a0 a1 a2)


def «cast:tupleKeysetExpression:keysetExpression» : tupleKeysetExpression → keysetExpression
  | .«`( % '&&&' % `)» a0 a1 => (.«`( % '&&&' % `)» a0 a1)
  | .«`( % '..' % `)» a0 a1 => (.«`( % '..' % `)» a0 a1)
  | .«`( DEFAULT `)»  => (.«`( DEFAULT `)» )
  | .«`( '_' `)»  => (.«`( '_' `)» )
  | .«`( % ',' % `)» a0 a1 => (.«`( % ',' % `)» a0 a1)


def «cast:tupleType:valueSetType» : tupleType → valueSetType
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)


def «cast:tupleTypeIR:typeIR» : tupleTypeIR → typeIR
  | .«TUPLE `< % `>» a0 => (.«TUPLE `< % `>» a0)


def «cast:tupleValue:value» : tupleValue → value
  | .«TUPLE `( % `)» a0 => (.«TUPLE `( % `)» a0)


def «cast:type:realTypeArgument» : type → realTypeArgument
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

end SpecTec
