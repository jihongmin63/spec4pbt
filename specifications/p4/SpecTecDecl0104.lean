import SpecTecDecl0103

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «cast:externFunctionTypeIR:callableTypeIR» : externFunctionTypeIR → callableTypeIR
  | .«EXTERN_FUNCTION % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_FUNCTION % `( % `) ':' %» a0 a1 a2)


def «cast:externMethodCallee:callee» : externMethodCallee → callee
  | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6 a7 a8 => (.«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» a0 a1 a2 a3 a4 a5 a6 a7 a8)


def «cast:externMethodDef:callableDef» : externMethodDef → callableDef
  | .«EXTERN_METHOD % `< % `> `( % `) %» a0 a1 a2 a3 => (.«EXTERN_METHOD % `< % `> `( % `) %» a0 a1 a2 a3)
  | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» a0 a1 a2 => (.«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» a0 a1 a2)


def «cast:externMethodPrototype:externConstructorOrMethodPrototype» : externMethodPrototype → externConstructorOrMethodPrototype
  | .«% % ';'» a0 a1 => (.«% % ';'» a0 a1)
  | .«% ABSTRACT % ';'» a0 a1 => (.«% ABSTRACT % ';'» a0 a1)


def «cast:externMethodTypeDefIR:callableTypeDefIR» : externMethodTypeDefIR → callableTypeDefIR
  | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)
  | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)


def «cast:externMethodTypeIR:callableTypeIR» : externMethodTypeIR → callableTypeIR
  | .«EXTERN_METHOD % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_METHOD % `( % `) ':' %» a0 a1 a2)
  | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» a0 a1 a2)


def «cast:externObject:object» : externObject → object
  | .«EXTERN % `< % `> `{ % % % `}» a0 a1 a2 a3 a4 => (.«EXTERN % `< % `> `{ % % % `}» a0 a1 a2 a3 a4)


def «cast:externObjectDeclaration:externDeclaration» : externObjectDeclaration → externDeclaration
  | .«% EXTERN % % `{ % `}» a0 a1 a2 a3 => (.«% EXTERN % % `{ % `}» a0 a1 a2 a3)


def «cast:externObjectDeclarationIR:declarationIR» : externObjectDeclarationIR → declarationIR
  | .«% EXTERN % `< % ',' `> `{ % % `}» a0 a1 a2 a3 a4 => (.«% EXTERN % `< % ',' `> `{ % % `}» a0 a1 a2 a3 a4)


def «cast:externObjectTypeDefIR:typeDefIR» : externObjectTypeDefIR → typeDefIR
  | .«EXTERN % `< % ',' % `> %» a0 a1 a2 a3 => (.«EXTERN % `< % ',' % `> %» a0 a1 a2 a3)


def «cast:externObjectTypeIR:typeIR» : externObjectTypeIR → typeIR
  | .«EXTERN % `< % `> %» a0 a1 a2 => (.«EXTERN % `< % `> %» a0 a1 a2)


def «cast:forInitStatementListNonEmpty:forInitStatementList» : forInitStatementListNonEmpty → forInitStatementList
  | .«% % % %» a0 a1 a2 a3 => (.«% % % %» a0 a1 a2 a3)
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% ',' %» a0 a1 => (.«% ',' %» a0 a1)


def «cast:forStatementIR:statementIR» : forStatementIR → statementIR
  | .«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % ';' % ';' % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4 => (.«% FOR `( % % IN % `) %» a0 a1 a2 a3 a4)
  | .«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5 => (.«% FOR `( % % % IN % `) %» a0 a1 a2 a3 a4 a5)


def «cast:forUpdateStatementIR:forInitStatementIR» : forUpdateStatementIR → forInitStatementIR
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:forUpdateStatementListNonEmpty:forUpdateStatementList» : forUpdateStatementListNonEmpty → forUpdateStatementList
  | .«% `( % `)» a0 a1 => (.«% `( % `)» a0 a1)
  | .«% `< % `> `( % `)» a0 a1 a2 => (.«% `< % `> `( % `)» a0 a1 a2)
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)
  | .«% ',' %» a0 a1 => (.«% ',' %» a0 a1)


def «cast:functionDeclaration:declaration» : functionDeclaration → declaration
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:functionDeclaration:objectDeclaration» : functionDeclaration → objectDeclaration
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:functionDeclarationIR:declarationIR» : functionDeclarationIR → declarationIR
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:functionDeclarationIR:objectDeclarationIR» : functionDeclarationIR → objectDeclarationIR
  | .«% % %» a0 a1 a2 => (.«% % %» a0 a1 a2)


def «cast:functionTypeDefIR:callableTypeDefIR» : functionTypeDefIR → callableTypeDefIR
  | .«FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)
  | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4 => (.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» a0 a1 a2 a3 a4)


def «cast:functionTypeIR:callableTypeIR» : functionTypeIR → callableTypeIR
  | .«FUNCTION % `( % `) ':' %» a0 a1 a2 => (.«FUNCTION % `( % `) ':' %» a0 a1 a2)
  | .«EXTERN_FUNCTION % `( % `) ':' %» a0 a1 a2 => (.«EXTERN_FUNCTION % `( % `) ':' %» a0 a1 a2)


def «cast:headerStackTypeIR:typeIR» : headerStackTypeIR → typeIR
  | .«HEADER_STACK % `[ % `]» a0 a1 => (.«HEADER_STACK % `[ % `]» a0 a1)


def «cast:headerStackValue:value» : headerStackValue → value
  | .«HEADER_STACK `[ % `( % `) `]» a0 a1 => (.«HEADER_STACK `[ % `( % `) `]» a0 a1)


def «cast:headerTypeDeclaration:derivedTypeDeclaration» : headerTypeDeclaration → derivedTypeDeclaration
  | .«% HEADER % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER % % `{ % `}» a0 a1 a2 a3)


def «cast:headerTypeDeclarationIR:declarationIR» : headerTypeDeclarationIR → declarationIR
  | .«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER % `< % `> `{ % `}» a0 a1 a2 a3)


def «cast:headerTypeDefIR:typeDefIR» : headerTypeDefIR → typeDefIR
  | .«HEADER % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER % `< % `> `{ % `}» a0 a1 a2)


def «cast:headerTypeIR:typeIR» : headerTypeIR → typeIR
  | .«HEADER % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER % `< % `> `{ % `}» a0 a1 a2)


def «cast:headerUnionTypeDeclaration:derivedTypeDeclaration» : headerUnionTypeDeclaration → derivedTypeDeclaration
  | .«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % % `{ % `}» a0 a1 a2 a3)


def «cast:headerUnionTypeDeclarationIR:declarationIR» : headerUnionTypeDeclarationIR → declarationIR
  | .«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3 => (.«% HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 a3)


def «cast:headerUnionTypeDefIR:typeDefIR» : headerUnionTypeDefIR → typeDefIR
  | .«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2)


def «cast:headerUnionTypeIR:typeIR» : headerUnionTypeIR → typeIR
  | .«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2 => (.«HEADER_UNION % `< % `> `{ % `}» a0 a1 a2)


def «cast:headerUnionValue:value» : headerUnionValue → value
  | .«HEADER_UNION % `{ % `}» a0 a1 => (.«HEADER_UNION % `{ % `}» a0 a1)

end SpecTec
