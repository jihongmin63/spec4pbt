import SpecTecDecl0126

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:methodTypeDefIR:externMethodTypeDefIR» : methodTypeDefIR → Bool
  | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:methodTypeDefIR:parserApplyMethodTypeIR» : methodTypeDefIR → Bool
  | .«PARSER_APPLY `( % `)» _ => true
  | _ => false


def «sub:methodTypeDefIR:tableApplyMethodTypeIR» : methodTypeDefIR → Bool
  | .«TABLE_APPLY ':' %» _ => true
  | _ => false


def «sub:nameList:name» : nameList → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | ._TID _ => true
  | .LIST => true
  | _ => false


def «sub:namedExpressionList:namedExpression» : namedExpressionList → Bool
  | .«% '=' %» _ _ => true
  | _ => false


def «sub:object:controlObject» : object → Bool
  | .«CONTROL `< % `> `( % `) `{ % % % % `}» _ _ _ _ _ _ => true
  | _ => false


def «sub:object:externObject» : object → Bool
  | .«EXTERN % `< % `> `{ % % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:object:packageObject» : object → Bool
  | .«PACKAGE `< % `> `{ % `}» _ _ => true
  | _ => false


def «sub:object:parserObject» : object → Bool
  | .«PARSER `< % `> `( % `) `{ % % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:object:tableObject» : object → Bool
  | .«TABLE % `{ % % `}» _ _ _ => true
  | _ => false


def «sub:object:valueSetObject» : object → Bool
  | .«VALUE_SET `{ % `( % `) `}» _ _ => true
  | _ => false


def «sub:objectDeclaration:functionDeclaration» : objectDeclaration → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:objectDeclaration:instantiation» : objectDeclaration → Bool
  | .«% % `( % `) % ';'» _ _ _ _ => true
  | .«% % `( % `) % % ';'» _ _ _ _ _ => true
  | _ => false


def «sub:objectDeclarationIR:functionDeclarationIR» : objectDeclarationIR → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «sub:objectDeclarationIR:instantiationIR» : objectDeclarationIR → Bool
  | .«% % % `( % `) % % ';'» _ _ _ _ _ _ => true
  | _ => false


def «sub:parameterInitializerIR:constantInitializerIR» : parameterInitializerIR → Bool
  | .«'=' _VALUE %» _ => true
  | _ => false


def «sub:parameterInitializerIR:initializerIR» : parameterInitializerIR → Bool
  | .«'=' %» _ => true
  | _ => false


def «sub:parameterList:nonEmptyParameterList» : parameterList → Bool
  | .«% % % % %» _ _ _ _ _ => true
  | .«% ',' %» _ _ => true
  | _ => false


def «sub:parameterList:parameter» : parameterList → Bool
  | .«% % % % %» _ _ _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatement:constantDeclaration» : parserBlockElementStatement → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatement:parserStatement» : parserBlockElementStatement → Bool
  | .«';'» => true
  | .«% % % ';'» _ _ _ => true
  | .«% `( % `) ';'» _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | .«% `{ % `}» _ _ => true
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatement:variableDeclaration» : parserBlockElementStatement → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatementIR:constantDeclarationIR» : parserBlockElementStatementIR → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatementIR:parserStatementIR» : parserBlockElementStatementIR → Bool
  | .«';'» => true
  | .«% % % ';'» _ _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | .«% `{ % `}» _ _ => true
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «sub:parserBlockElementStatementIR:variableDeclarationIR» : parserBlockElementStatementIR → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclaration:constantDeclaration» : parserLocalDeclaration → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclaration:instantiation» : parserLocalDeclaration → Bool
  | .«% % `( % `) % ';'» _ _ _ _ => true
  | .«% % `( % `) % % ';'» _ _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclaration:valueSetDeclaration» : parserLocalDeclaration → Bool
  | .«% VALUE_SET `< % `> `( % `) % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclaration:variableDeclaration» : parserLocalDeclaration → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclarationIR:constantDeclarationIR» : parserLocalDeclarationIR → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclarationIR:instantiationIR» : parserLocalDeclarationIR → Bool
  | .«% % % `( % `) % % ';'» _ _ _ _ _ _ => true
  | _ => false


def «sub:parserLocalDeclarationIR:valueSetDeclarationIR» : parserLocalDeclarationIR → Bool
  | .«% VALUE_SET `< % `> `( % `) % ';'» _ _ _ _ => true
  | _ => false

end SpecTec
